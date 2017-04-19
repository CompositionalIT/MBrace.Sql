#load "SqlParser.fsx"
#load "StandardLibrary.fsx"

#r """packages/Streams/lib/net45/Streams.dll"""
#r """packages/FsPickler/lib/net45/FsPickler.dll"""
#r """packages/FsPickler.Json/lib/net45/FsPickler.Json.dll"""
#r """packages/Vagabond/lib/net45/Vagabond.dll"""
#r """packages/MBrace.Core/lib/net45/MBrace.Core.dll"""
#r """packages/MBrace.Flow/lib/net45/MBrace.Flow.dll"""
#r """packages/MBrace.Runtime/lib/net45/MBrace.Runtime.dll"""

module Transpiler =
    module Str = String

    open SqlParser.Ast
    open MBrace.Flow
    open MBrace.Core
    open MBrace.Core.Internals
    open StandardLibrary.StdLib.Extractors
    open StandardLibrary.StdLib.Writers
    open System.Text.RegularExpressions
    open System
    open StandardLibrary
    open StandardLibrary.StdLib
    open System.Threading
    open System.IO
    let private cloudFlowStaticId = mkUUID ()

    type QueryOutput =
        | Files of CloudFileInfo []
        | Memory
        | Array of Map<string, SqlType> []

    let toCloudFilesWithWriter (fileStore:ICloudFileStore) (dirPath:string) (retrieveWriter:Stream -> IWriter) (flow:CloudFlow<Map<string, SqlType>>) =
        let collectorF (cloudCt:ICloudCancellationToken) =
            local {
                let cts = CancellationTokenSource.CreateLinkedTokenSource(cloudCt.LocalToken)
                let results = ResizeArray<string * IWriter>()
                fileStore.CreateDirectory(dirPath) |> Async.RunSync
                return {
                    new Collector<Map<string, SqlType>, CloudFileInfo []> with
                        member self.DegreeOfParallelism = flow.DegreeOfParallelism
                        member self.Iterator () =
                            let path = fileStore.Combine(dirPath, sprintf "Part-%s-%s" cloudFlowStaticId (mkUUID ()))
                            let writer = fileStore.BeginWrite(path) |> Async.RunSync |> retrieveWriter
                            results.Add((path, writer))
                            {   Func = (fun row -> writer.WriteRecord row);
                                Cts = cts }
                        member self.Result =
                            results |> Seq.iter (fun (_, writer) -> writer.Dispose())
                            results |> Seq.map (fun (path, _) -> CloudFileInfo(fileStore, path)) |> Seq.toArray }
            }
        cloud {
            let! ct = Cloud.CancellationToken
            use! cts = Cloud.CreateCancellationTokenSource(ct)
            return! flow.WithEvaluators (collectorF cts.Token) (fun cloudFiles -> local { return cloudFiles }) (fun result -> local { return Array.concat result })
        }

    let private buildDestination cloudFileStore (destinationEx:DestinationEx) (cf:CloudFlow<Map<string, SqlType>>) =
        match destinationEx with
        | ResultSet name ->
            cloud {
                let! pcf = cf |> CloudFlow.persist StorageLevel.Disk
                let! d = CloudDictionary.GetById<PersistedCloudFlow<Map<string, SqlType>>>("MBraceSqlResults")
                do! d.AddOrUpdateAsync(name, fun i -> pcf) |> Async.Ignore |> Cloud.OfAsync
                return Memory
            }
        | Folder(folderName, Writer(writerName)) ->
            cloud {
                let retrieveWriter = StdLib.Writers.RetrieveWriterByName writerName Map.empty
                let! files = toCloudFilesWithWriter cloudFileStore folderName retrieveWriter cf
                return Files files
            }

    let private buildOriginQuery (From(origin, alias)) =
        match origin with
        | OriginEx.ResultSet rsName ->
            local {
                let! d = MBrace.Core.CloudDictionary.GetById<PersistedCloudFlow<Map<string, SqlType>>>("MBraceSqlResults")
                let! cf = d.TryFindAsync(rsName) |> Cloud.OfAsync
                return cf |> Option.map (fun t -> t :> CloudFlow<_>)
                // let flow =
                //     [|
                //         ["user.age", SqlType.Integer 24; "user.name", SqlType.String "Anthony Brown"; "user.username", SqlType.String "bruinbrown93"] |> Map.ofList
                //         ["user.age", SqlType.Integer 40; "user.name", SqlType.String "Isaac Abraham"; "user.username", SqlType.String "isaac_abraham"] |> Map.ofList
                //         ["user.age", SqlType.Integer 33; "user.name", SqlType.String "Prashant Pathak"; "user.username", SqlType.String "pathakattack"] |> Map.ofList
                //     |] |> CloudFlow.OfArray |> Some
                // return flow
            }
        | OriginEx.DataSource (fileName, Extractor(extractor)) ->
            local {
                //TODO:Using the extractor we retrieve here we then use the CloudFlow.OfCloudFiles and pipe it through the extractor
                let extractor = RetrieveExtractorByName extractor Map.empty
                let! fileExists = CloudFile.Exists(fileName)
                let! directoryExists = CloudDirectory.Exists(fileName)
                if fileExists then
                    return
                        CloudFlow.OfCloudFiles([fileName], extractor.Extract)
                        |> Some
                else if directoryExists then
                    return
                        CloudFlow.OfCloudDirectory(fileName, extractor.Extract)
                        |> Some
                else
                    return None
            }

    let private buildJoinQuery (joins:JoinEx list) (primaryFlow:CloudFlow<Map<string, SqlType>>) =
        ()

    let private buildFilterQuery (filter:TermEx) (cloudFlow:CloudFlow<Map<string, SqlType>>) =
        let truth = SqlType.Bool true
        cloudFlow
        |> CloudFlow.filter (fun row ->
            truth = evaluateTerm row filter)

    let rec buildProjections (cloudFlow:CloudFlow<Map<string, SqlType>>) (projections:ProjectionEx list) =
        let applyProjectionToRow (projections:ProjectionEx list) (row:Map<string, SqlType>) =
            projections
            |> List.fold (fun s t ->
                let (Projection(term, alias)) = t//I honestly can't remember why I did this, I think it's because a table or column reference can be computed in SQL e.g. SELECT * FROM ("Table" + "A"). Never mind, there's three types of projections and we already deal with 2 of them before this.
                match term with
                | Ref components ->
                    let str = components |> String.concat "."
                    if str = "*" then
                        row
                    else
                        let name = defaultArg alias str
                        s |> Map.add name row.[str]
                | _ ->
                    let res = evaluateTerm row term
                    let name = defaultArg alias (string res)
                    s |> Map.add name res) Map.empty

        match projections with
        | [Distinct(projections)] ->
            let cf =
                cloudFlow
                |> CloudFlow.distinct
            buildProjections cf projections
        | [Top(count, projections)] ->
            let cf =
                cloudFlow
                |> CloudFlow.take count
            buildProjections cf projections
        | projections ->
            cloudFlow
            |> CloudFlow.map (applyProjectionToRow projections)

    let buildOrder (flow:CloudFlow<Map<string, SqlType>>) (sort:OrderEx list) =
        let projections, sorter =
            sort
            |> List.map (fun (Order (column, direction)) -> column, match direction with Some(ASC) | None -> (<) | Some(DESC) -> (>))
            |> List.unzip
        CloudFlow.sortByUsing 

    let TranspileSqlAstToCloudFlow cloudFileStore (sqlAst:Query) =
        let defaultArg t opt = defaultArg opt t
        cloud {
            let! origin = buildOriginQuery sqlAst.From
            match origin with
            | Some origin ->
                let filtered =
                    sqlAst.Filters
                    |> Option.map (fun t -> buildFilterQuery t origin)
                    |> defaultArg origin

                let projected =
                    buildProjections filtered sqlAst.Projection

                // let sorted =
                //     buildOrder projected sqlAst.Order

                match sqlAst.Destination with
                | Some dest ->
                    return! buildDestination cloudFileStore dest projected
                | None ->
                    let! res = projected |> CloudFlow.toArray
                    return Array res

                //TODO: The next stage to go in here is join, then group by, then having

            | None ->
                return invalidOp "No file or directory was found matching the supplied path"
        }

(*
    The order of operations which should happen within the transpilation is as follows
        0. From - Build up origin datasets
        1. Join - Ensures that the complete row is available for all subsequent queries
        2. Group by - Allows verification of projections during subsequent stages and checks to see which function should be used e.g. CloudFlow.Sum or Seq.sum
        3. Filter - If it's grouped then this is in the form of a HAVING expression, otherwise it's a regular where (Having requires changes to the Sql Parser
        4. Order - Having filtered we can now order the results, we need to specify the max number to use here as well
        5. Projections - The dataset should now be projected into the column names specified in the select query
        6. Destination - Finally add the destination
*)

open Transpiler

[<AutoOpen>]
module CloudClientExtensions =
    open MBrace.Core
    open MBrace.Core.Internals
    open MBrace.Runtime
    open Transpiler
    open SqlParser.Parser
    open SqlParser.Ast

    let convertSqlToCloudFlow fileStore sql =
        let res = parse sql
        match res with
        | QueryEx q -> TranspileSqlAstToCloudFlow fileStore q
        | _ -> failwith "Unsupported query type"

    type MBrace.Runtime.MBraceClient with
        member this.ExecuteSql(sql:string) =
            let fileStore = this.GetResource<ICloudFileStore>()
            convertSqlToCloudFlow fileStore sql
            |> this.Run

        member this.ExecuteSqlAsync(sql:string) =
            let fileStore = this.GetResource<ICloudFileStore>()
            convertSqlToCloudFlow fileStore sql
            |> this.RunAsync