#load "SqlParser.fsx"

#r """packages/CsvHelper/lib/net45/CsvHelper.dll"""
#r """packages/Newtonsoft.Json/lib/net45/Newtonsoft.Json.dll"""
#r """packages/MBrace.Flow/lib/net45/MBrace.Flow.dll"""
#r """packages/MBrace.Core/lib/net45/MBrace.Core.dll"""
#r """packages/Streams/lib/net45/Streams.dll"""

module StdLib =

    open System
    open SqlParser.Ast
    open System.Text.RegularExpressions
    module Str = Microsoft.FSharp.Core.String

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
        | UnEx(Like, _) -> SqlType.Null
        | Call(fnName, arguments) -> SqlType.Null
        | Case(defaultCase, branches, defaultValue) -> SqlType.Null
        | QueryEx(query) -> SqlType.Null

    module Extractors =
        open System.IO
        open Newtonsoft.Json
        open Newtonsoft.Json.Linq

        type IExtractor =
            abstract Extract : System.IO.Stream -> seq<Map<string, SqlType>>

        let rec collapseJson (json:JToken) =
            match json.Type with
            | JTokenType.Object ->
                [for t in json.Children<JProperty>() do
                    yield! collapseJson t.Value]
            | JTokenType.Boolean ->
                [json.Path, SqlType.Bool(json.Value<bool>())]
            | JTokenType.Bytes ->
                [json.Path, SqlType.Binary(json.Value<byte []>())]
            | JTokenType.Float ->
                [json.Path, SqlType.Float(json.Value<float>())]
            | JTokenType.Integer ->
                [json.Path, SqlType.Integer(json.Value<int>())]
            | JTokenType.Null ->
                [json.Path, SqlType.Null]
            | JTokenType.String ->
                [json.Path, SqlType.String(json.Value<string>())]
            | _ -> []

        type CsvExtractor(options:Map<string, string>) =
            let encoding = defaultArg (options |> Map.tryFind "encoding") "UTF-8"
            let hasHeaders = defaultArg (options |> Map.tryFind "headers" |> Option.map System.Convert.ToBoolean) false

            interface IExtractor with
                member this.Extract stream =
                    let streamReader = new System.IO.StreamReader(stream)
                    let csvReader = new CsvHelper.CsvReader(streamReader)
                    let headers = 
                        if hasHeaders then
                            csvReader.ReadHeader() |> ignore
                            csvReader.FieldHeaders
                        else
                            let record = csvReader.CurrentRecord
                            [| 1 .. record.Length |] |> Array.map string
                    let rows =
                        seq {
                            while csvReader.Read() do
                                for i in 0..headers.Length - 1 do
                                    let row = csvReader.CurrentRecord
                                    yield
                                        row
                                        |> Array.map SqlType.String
                                        |> Array.zip headers
                                        |> Map.ofArray
                        }
                    rows

        type JsonLExtractor(properties:Map<string, string>) =
            interface IExtractor with
                member this.Extract stream =
                    use streamReader = new StreamReader(stream)
                    [|
                        while not streamReader.EndOfStream do
                            let line = streamReader.ReadLine()
                            let json = JObject.Parse(line)
                            yield collapseJson (json) |> Map.ofList
                    |] :> _

        type JsonExtractor(properties:Map<string, string>) =
            interface IExtractor with
                member this.Extract stream =
                    use streamReader = new StreamReader(stream)
                    [|
                        let content = streamReader.ReadToEnd()
                        let json = JObject.Parse(content)
                        yield collapseJson json |> Map.ofList
                    |] :> _

        let RetrieveExtractorByName (name:string) properties : IExtractor =
            match name.ToLower() with
            | "csv" -> CsvExtractor(properties) :> _
            | "jsonl" -> JsonLExtractor(properties) :> _
            | "json" -> JsonExtractor(properties) :> _
            | _ -> invalidArg "name" "There's no extractor by that name"

    module Writers =
        open System.IO
        open MBrace.Flow
        open MBrace.Core
        open System.Threading
        open System.Collections.Generic
        // open Sql.Ast

        // let toCloudFilesWithSerializer (dirPath:string) serializer (flow:CloudFlow<Map<string, SqlType>>) =
        //     let collectorf (cloudCt : ICloudCancellationToken) =
        //         local {
        //             let cts = CancellationTokenSource.CreateLinkedTokenSource(cloudCt.LocalToken)
        //             let results = new List<string * StreamWriter>()
        //             let! _ = CloudDirectory.Create dirPath
        //             return
        //                 { new Collector<string, CloudFileInfo []> with
        //                     member self.DegreeOfParallelism = flow.DegreeOfParallelism
        //                     member self.Iterator() =
        //                         let path = CloudStore.Combine(dirPath, sprintf "Part-%s-%s.txt" cloudFlowStaticId (mkUUID ()))
        //                         let stream = store.BeginWrite(path) |> Async.RunSync
        //                         let writer = new StreamWriter(stream)
        //                         results.Add((path, writer))
        //                         {   Func = (fun line -> writer.WriteLine(line));
        //                             Cts = cts }
        //                     member self.Result =
        //                         results |> Seq.iter (fun (_, writer) -> writer.Dispose())
        //                         results |> Seq.map (fun (path, _) -> new CloudFileInfo(store, path)) |> Seq.toArray }
        //         }
        //     cloud {
        //         let! ct = Cloud.CancellationToken
        //         use! cts = Cloud.CreateCancellationTokenSource(ct)
        //         return! flow.WithEvaluators (collectorf cts.Token) (fun cloudFiles -> local { return cloudFiles }) (fun result -> local { return Array.concat result })
        //     }

        type IWriter = 
            abstract Write : Stream -> seq<Map<string, SqlType>> -> unit

    module Functions =
        let Len str =
            String.length str

        let Char i =
            (char i)