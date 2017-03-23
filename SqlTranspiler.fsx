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

    [<RequireQualifiedAccessAttribute>]
    type SqlType =
        | Bool of bool
        | String of string
        | Integer of int
        | Float of float
        | DateTime of DateTime
        | Binary of byte[]
        | Char of char
        | Money of decimal
        | Null
        member this.InnerValue =
            match this with
            | String v -> box v
            | Float v -> box v
            | Integer v -> box v
            | Bool v -> box v
            | DateTime dt -> box dt
            | Binary bin -> box bin
            | Char c -> box c
            | Money m -> box m
            | Null -> null
        static member (~-) v =
            match v with
            | Float v -> Float (-v)
            | Integer v -> Integer(-v)
            | Money m -> Money(-m)
            | _ -> invalidOp "The type does not support the - operator"

        static member (+) (left, right) =
            match left, right with
            | Float f1, Float f2 -> Float(f1 + f2)
            | Integer i1, Integer i2 -> Integer(i1 + i2)
            | _, _ -> sprintf "Unable to perform op (+) on types %A and %A" (left.GetType()) (right.GetType()) |> invalidOp

        static member (-) (left, right) =
            match left, right with
            | Integer i1, Integer i2 -> Integer(i1 - i2)
            | Float f1, Float f2 -> Float(f1 - f2)
            | _, _ -> sprintf "Unable to perform op (-) on types %A and %A" (left.GetType()) (right.GetType()) |> invalidOp

        static member (/) (left, right) =
            match left, right with
            | Integer i1, Integer i2 -> Integer(i1 / i2)
            | Float f1, Float f2 -> Float(f1 / f2)
            | _, _ -> sprintf "Unable to perform op (/) on types %A and %A" (left.GetType()) (right.GetType()) |> invalidOp

        static member (*) (left, right) =
            match left, right with
            | Integer i1, Integer i2 -> Integer(i1 * i2)
            | Float f1, Float f2 -> Float(f1 * f2)
            | _ -> sprintf "Unable to perform op (*) on types %A and %A" (left.GetType()) (right.GetType()) |> invalidOp

        static member (%) (left, right) =
            match left, right with
            | Integer i1, Integer i2 -> Integer(i1 % i2)
            | _ -> sprintf "Unable to perform op (%%) on types %A and %A" (left.GetType()) (right.GetType()) |> invalidOp

    let rec evaluateTerm (currentRow:Map<string, SqlType>) (term:TermEx) : SqlType =
        let evaluateTerm = evaluateTerm currentRow
        match term with
        | BinEx(BinOp.Eq, left, UnEx(Like, right)) ->
            let (SqlType.String left) = left |> evaluateTerm
            let (SqlType.String right) = right |> evaluateTerm
            SqlType.Bool (Regex.IsMatch(left, right))
        | BinEx (op, left, right) ->
            let left = evaluateTerm left
            let right = evaluateTerm right
            match op with
            | BinOp.Add -> left + right
            | BinOp.Mul -> left * right
            | BinOp.Div -> left / right
            | BinOp.Eq -> SqlType.Bool(left = right)
            | BinOp.Gt -> SqlType.Bool (left > right)
            | BinOp.Gte -> SqlType.Bool (left >= right)
            | BinOp.Lt -> SqlType.Bool (left < right)
            | BinOp.Lte -> SqlType.Bool (left <= right)
            | BinOp.Mod -> left % right
            | BinOp.Sub -> left - right
        | And(left, right) ->
            let left = evaluateTerm left
            let right = evaluateTerm right
            match left, right with
            | SqlType.Bool b1, SqlType.Bool b2 -> SqlType.Bool(b1 && b2)
            | _, _ -> invalidOp "Can't compare different types"
        | Or(left, right) ->
            let left = evaluateTerm left
            let right = evaluateTerm right
            match left, right with
            | SqlType.Bool b1, SqlType.Bool b2 -> SqlType.Bool(b1 || b2)
            | _, _ -> invalidOp "Can't compare different types"
        | Not term ->
            let (SqlType.Bool(term)) = evaluateTerm term
            SqlType.Bool(not term)
        | UnEx(Neg, term) ->
            let term = evaluateTerm term
            -term
        | Value v ->
            match v with
            | ValueEx.Bool b -> SqlType.Bool b
            | Float f -> SqlType.Float f
            | Integer i -> SqlType.Integer i
            | Null -> SqlType.Null
            | String s -> SqlType.String s
        | Ref(elements) ->
            let elementName = elements |> Str.concat "."
            currentRow.[elementName]
        | Cast(term, typ) ->
            let term = evaluateTerm term
            match typ.ToUpper() with
            | "BOOL" -> 
                term.InnerValue
                |> System.Convert.ToBoolean
                |> SqlType.Bool
            | "INT" ->
                term.InnerValue
                |> System.Convert.ToInt32
                |> SqlType.Integer
            | "FLOAT" ->
                term.InnerValue
                |> System.Convert.ToDouble
                |> SqlType.Float
            | "VARCHAR" ->
                term.InnerValue
                |> string
                |> SqlType.String
            //TODO: Implement any other SQL types which might be needed here
            | _ -> term
        (*| Call(fnName, arguments) -> ()*)
        | _ -> SqlType.Null

    let private buildDestination (destinationEx:DestinationEx) (cf:CloudFlow<Map<string, ValueEx>>) =
        match destinationEx with
        | ResultSet name ->
            cloud {
                let! pcf = cf |> CloudFlow.persist StorageLevel.Disk
                let! d = CloudDictionary.GetById<PersistedCloudFlow<Map<string, ValueEx>>>("__MBrace.Sql.Results")
                do! d.ForceAddAsync(name, pcf) |> Cloud.OfAsync
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
                // let! d = MBrace.Core.CloudDictionary.GetById<PersistedCloudFlow<Map<string, SqlType>>>("__MBrace.Sql.Results")
                // let! cf = d.TryFindAsync(rsName) |> Cloud.OfAsync
                // let cf =
                //     cf
                //     |> Option.map (fun t -> t :> CloudFlow<Map<string, SqlType>>)
                // return cf
                let flow =
                    [|
                        ["user.age", SqlType.Integer 24; "user.name", SqlType.String "Anthony Brown"; "user.username", SqlType.String "bruinbrown93"] |> Map.ofList
                        ["user.age", SqlType.Integer 40; "user.name", SqlType.String "Isaac Abraham"; "user.username", SqlType.String "isaac_abraham"] |> Map.ofList
                        ["user.age", SqlType.Integer 33; "user.name", SqlType.String "Prashant Pathak"; "user.username", SqlType.String "pathakattack"] |> Map.ofList
                    |] |> CloudFlow.OfArray |> Some
                return flow
            }
        | OriginEx.DataSource (fileName, Extractor(extractor)) ->
            local {
                //TODO:Using the extractor we retrieve here we then use the CloudFlow.OfCloudFiles and pipe it through the extractor
                let extractor = RetrieveExtractorByName extractor
                let! fileExists = CloudFile.Exists(fileName)
                let! directoryExists = CloudDirectory.Exists(fileName)
                if fileExists then
                    return Some(Unchecked.defaultof<CloudFlow<Map<string, SqlType>>>)
                else if directoryExists then
                    return Some(Unchecked.defaultof<CloudFlow<Map<string, SqlType>>>)
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
                let (Projection(Ref components, alias)) = t //I honestly can't remember why I did this, I think it's because a table or column reference can be computed in SQL e.g. SELECT * FROM ("Table" + "A")
                let str = components |> String.concat "."
                if str = "*" then
                    row
                else
                    let name = defaultArg alias str
                    s |> Map.add name row.[name]) Map.empty

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

                //TODO: I'm not sure if there's any other stages that need to happen here. I think we need to do group by and having

                return projected
            | None ->
                return invalidOp "No file or directory was found matching the supplied path"
        }

// open Transpiler

// [<AutoOpen>]
// module CloudClientExtensions =
//     open MBrace.Core
//     open MBrace.Runtime
//     open Transpiler
//     open Sql
//     open Sql.Ast

//     type MBrace.Runtime.MBraceClient with
//         member this.ExecuteSql(sql:string) =
//             let res = Sql.Parser.parse sql
//             let clo =
//                 match res with
//                 | QueryEx q -> TranspileSqlAstToCloudFlow q
//                 //TODO: Some of the other SQL types we'll have in here are DROP and CREATE TABLE etc
//                 //TODO: The output also needs changing to reflect whether we're returning a vector, scalar or non query
//                 | _ -> failwith "Unsupported query type used"
//             this.Run(clo)


open SqlParser.Ast
open Transpiler

let orTest = TermEx.Or(TermEx.Value(ValueEx.Bool(false)), TermEx.Value(ValueEx.Bool(true)))
let andTest = TermEx.And(TermEx.Value(ValueEx.Bool(true)), TermEx.Value(ValueEx.Bool(true)))
let addTest = TermEx.BinEx(BinOp.Add, TermEx.Value(ValueEx.Integer(5)), TermEx.Value(ValueEx.Integer(7)))
let refAddTest = TermEx.BinEx(BinOp.Add, TermEx.Ref(["user"; "likecount"]), TermEx.Ref(["user"; "retweetcount"]))
let regexTest = BinEx(BinOp.Eq, Value(ValueEx.String "bruinbrown"), UnEx(Like, Value(ValueEx.String "bruin.*")))
let equalityTest = BinEx(BinOp.Eq, Value(ValueEx.Bool true), Value(ValueEx.Bool true))
let castTest = Cast(Value(ValueEx.Integer 5), "VARCHAR")
let userTwitterData = ["user.likecount", SqlType.Integer 27; "user.retweetcount", SqlType.Integer 32; "user.username", SqlType.String "bruinbrown"] |> Map.ofList

let result = evaluateTerm userTwitterData castTest

let parsed = SqlParser.Parser.parse "SELECT * FROM #test"

open MBrace.Core
let job =
    cloud {
        let! cf =
            match parsed with
            | TermEx.QueryEx query -> TranspileSqlAstToCloudFlow query
            | _ -> invalidOp "It's all gone Pete Tong"
        return! cf |> MBrace.Flow.CloudFlow.toArray
    }

open MBrace.ThreadPool
let tp = ThreadPoolRuntime.Create()
let res = tp.RunSynchronously(job)