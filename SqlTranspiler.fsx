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
    open StandardLibrary.StdLib.Extractors
    open System.Text.RegularExpressions
    open System
    open StandardLibrary
    open StandardLibrary.StdLib

    let private buildDestination (destinationEx:DestinationEx) (cf:CloudFlow<Map<string, SqlType>>) =
        match destinationEx with
        | ResultSet name ->
            cloud {
                let! pcf = cf |> CloudFlow.persist StorageLevel.Disk
                let! d = CloudDictionary.GetById<PersistedCloudFlow<Map<string, SqlType>>>("MBraceSqlResults")
                do! d.AddOrUpdateAsync(name, fun i -> pcf) |> Async.Ignore |> Cloud.OfAsync
            } :> Cloud<_>
        | Folder(string, writer) ->
            cloud {
                //TODO: This needs to take in the writer that's provided and output the partitions of the dataset into the folder specified
                return ()
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

    let private buildFilterQuery (filter:TermEx) (cloudFlow:CloudFlow<Map<string, SqlType>>) =
        let truth = SqlType.Bool true
        cloudFlow
        |> CloudFlow.filter (fun row ->
            truth = evaluateTerm row filter)

    let rec buildProjections (cloudFlow:CloudFlow<Map<string, SqlType>>) (projections:ProjectionEx list) =
        let applyProjectionToRow (projections:ProjectionEx list) (row:Map<string, SqlType>) =
            projections
            |> List.fold (fun s t ->
                let (Projection(term, alias)) = t //I honestly can't remember why I did this, I think it's because a table or column reference can be computed in SQL e.g. SELECT * FROM ("Table" + "A")
                match term with
                | Ref components ->
                    let str = components |> String.concat "."
                    if str = "*" then
                        row
                    else
                        let name = defaultArg alias str
                        s |> Map.add name row.[name]
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

    type QueryOutput =
        | Files
        | Memory
        | Array of Map<string, SqlType> []

    let TranspileSqlAstToCloudFlow (sqlAst:Query) =
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

                match sqlAst.Destination with
                | Some dest ->
                    let! res = buildDestination dest projected
                    return Files
                | None ->
                    let! res = projected |> CloudFlow.toArray
                    return Array res

                //TODO: The next stage to go in here is join, then group by, then having

            | None ->
                return invalidOp "No file or directory was found matching the supplied path"
        }

// open Transpiler

// [<AutoOpen>]
// module CloudClientExtensions =
//     open MBrace.Core
//     open MBrace.Core.Internals
//     open MBrace.Runtime
//     open Transpiler
//     open SqlParser.Parser
//     open SqlParser.Ast

//     type MBrace.Runtime.MBraceClient with
//         member this.ExecuteSql(sql:string) =
//             let res = parse sql
//             let cluster = this.GetResource<ICloudFileStore>()
//             let clo =
//                 match res with
//                 | QueryEx q -> TranspileSqlAstToCloudFlow q
//                 //TODO: Some of the other SQL types we'll have in here are DROP and CREATE TABLE etc
//                 //TODO: The output also needs changing to reflect whether we're returning a vector, scalar or non query
//                 | _ -> failwith "Unsupported query type used"
//             this.Run(clo)


