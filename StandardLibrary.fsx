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

    let private truth = SqlType.Bool true

    let rec shrinkAst (term:TermEx) : TermEx =
        match term with
        | BinEx(BinOp.Eq, TermEx.Value v1, TermEx.Value v2) ->
            TermEx.Value(ValueEx.Bool(v1 = v2))
        | BinEx(BinOp.Lt, TermEx.Value v1, TermEx.Value v2) ->
            TermEx.Value(ValueEx.Bool(v1 < v2))
        | BinEx(BinOp.Lte, TermEx.Value v1, TermEx.Value v2) ->
            TermEx.Value(ValueEx.Bool(v1 <= v2))
        | BinEx(BinOp.Add, TermEx.Value v1, TermEx.Value v2) ->
            TermEx.Value(v1 + v2)
        | BinEx(BinOp.Div, TermEx.Value v1, TermEx.Value v2) ->
            TermEx.Value(v1 / v2)
        | BinEx(BinOp.Gt, TermEx.Value v1, TermEx.Value v2) ->
            TermEx.Value(ValueEx.Bool(v1 > v2))
        | BinEx(BinOp.Gte, TermEx.Value v1, TermEx.Value v2) ->
            TermEx.Value(ValueEx.Bool(v1 <= v2))
        | BinEx(BinOp.Mul, TermEx.Value v1, TermEx.Value v2) ->
            TermEx.Value(v1 * v2)
        | BinEx(BinOp.Mod, TermEx.Value v1, TermEx.Value v2) ->
            TermEx.Value(v1 % v2)
        | And(TermEx.Value(ValueEx.Bool b1), TermEx.Value(ValueEx.Bool b2)) ->
            TermEx.Value(ValueEx.Bool(b1 && b2))
        | Or(TermEx.Value(ValueEx.Bool b1), TermEx.Value(ValueEx.Bool b2)) ->
            TermEx.Value(ValueEx.Bool(b1 || b2))
        | Not(TermEx.Value(ValueEx.Bool b)) ->
            TermEx.Value(ValueEx.Bool (not b))
        | _ -> term
    
    let mapType = typeof<Map<string, SqlType>>
    let mapGetter = mapType.GetProperty("Item")

    let compileSqlAst (term:TermEx) =
        let functionParameter = Quotations.Var("currentRow", typeof<Map<string, SqlType>>)
        let rec convertAstToQuotation (term:TermEx) : Quotations.Expr<SqlType> =
            match term with
            | TermEx.Value v ->
                match v with
                | ValueEx.Bool b -> <@ SqlType.Bool b @>
                | ValueEx.Float f -> <@ SqlType.Float f @>
                | ValueEx.Integer i -> <@ SqlType.Integer i @>
                | ValueEx.Null -> <@ SqlType.Null @>
                | ValueEx.String s -> <@ SqlType.String s @>
            | BinEx(BinOp.Eq, left, UnEx(UnOp.Like, right)) ->
                <@
                    let left = %convertAstToQuotation left
                    let right = %convertAstToQuotation right
                    match left, right with
                    | SqlType.String field, SqlType.String pattern ->
                        let regex = System.Text.RegularExpressions.Regex(pattern)
                        field
                        |> regex.IsMatch
                        |> SqlType.Bool
                    | _ -> sprintf "Unable to perform regex match on types %A and %A" (left.GetType()) (right.GetType()) |> invalidOp
                @>
            | BinEx(BinOp.Eq, left, Not(Value(ValueEx.Null))) ->
                <@
                    let left = %convertAstToQuotation left
                    match left with
                    | SqlType.Null -> SqlType.Bool false
                    | _ -> SqlType.Bool true
                @>
            | BinEx(BinOp.Eq, left, Value(ValueEx.Null)) ->
                <@
                    let left = %convertAstToQuotation left
                    match left with
                    | SqlType.Null -> SqlType.Bool true
                    | _ -> SqlType.Bool false
                @>
            | BinEx(op, left, right) ->
                let left = convertAstToQuotation left
                let right = convertAstToQuotation right
                match op with
                | BinOp.Add -> <@ %left + %right @>
                | BinOp.Div -> <@ %left / %right @>
                | BinOp.Eq -> <@ SqlType.Bool(%left = %right) @>
                | BinOp.Gt -> <@ SqlType.Bool(%left > %right) @>
                | BinOp.Gte -> <@ SqlType.Bool(%left >= %right) @>
                | BinOp.Lt -> <@ SqlType.Bool(%left < %right) @>
                | BinOp.Lte -> <@ SqlType.Bool(%left <= %right) @>
                | BinOp.Mod -> <@ %left % %right @>
                | BinOp.Mul -> <@ %left * %right @>
                | BinOp.Sub -> <@ %left - %right @>
            | TermEx.And(left, right) ->
                <@
                    let left = %convertAstToQuotation left
                    let right = %convertAstToQuotation right
                    match left, right with
                    | SqlType.Bool b1, SqlType.Bool b2 -> SqlType.Bool(b1 && b2)
                    | _ -> sprintf "Unable to perform op (&&) on types %A and %A" (left.GetType()) (right.GetType()) |> invalidOp
                @>
            | TermEx.Not(term) ->
                <@ 
                    let expr = %convertAstToQuotation term
                    match expr with
                    | SqlType.Bool b -> SqlType.Bool (not b)
                    | _ -> sprintf "Unable to perform op (not) on type %A" (expr.GetType()) |> invalidOp
                @>
            | TermEx.Or(left, right) ->
                <@
                    let left = %convertAstToQuotation left
                    let right = %convertAstToQuotation right
                    match left, right with
                    | SqlType.Bool b1, SqlType.Bool b2 -> SqlType.Bool(b1 || b2)
                    | _ -> sprintf "Unable to perform op (||) on types %A and %A" (left.GetType()) (right.GetType()) |> invalidOp
                @>
            | TermEx.Ref(components) ->
                let elementName = components |> Str.concat "."
                Quotations.Expr.Cast<SqlType>(Quotations.Expr.PropertyGet(Quotations.Expr.Var functionParameter, mapGetter, [Quotations.Expr.Value elementName]))
            | TermEx.UnEx(UnOp.Neg, term) ->
                <@ 
                    let term = %convertAstToQuotation term
                    -term 
                @>
            | Call("CAST", [Cast (term, typ)])
            | Cast(term, typ) ->
                <@
                    let term = %convertAstToQuotation term
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
                @>
            | TermEx.QueryEx _ ->
                sprintf "Nested queries are not currently supported" |> invalidOp
            | TermEx.Case(selector, branches, defaultValue) ->
                let rec findFirstResult (branches:(Quotations.Expr<SqlType>*Quotations.Expr<SqlType>) list) (selector:Quotations.Expr<SqlType>) defaultValue =
                    match branches with
                    | (branch, result)::xs ->
                        <@
                            if %branch = %selector then
                                %result
                            else %findFirstResult xs selector defaultValue
                        @>
                    | [] -> defaultValue
                let selector =
                    match selector with
                    | Some x -> convertAstToQuotation x
                    | None -> <@ SqlType.Bool true @>
                let defaultValue = convertAstToQuotation defaultValue
                let branches =
                    branches
                    |> List.map (fun (a,b) -> convertAstToQuotation a, convertAstToQuotation b)
                findFirstResult branches selector defaultValue

        let lambdaBody = convertAstToQuotation term
        Quotations.Expr.Lambda(functionParameter, lambdaBody)
        
    let ast = Ref(["Test"])

    let rec evaluateTerm (currentRow:Map<string, SqlType>) (term:TermEx) : SqlType =
        //TODO: This is actually really computationally expensive and could be sped up a lot
        //It's a hard solution but dynamic method generation would be a good fit here
        //Supply a TermEx, collapse it and generate an IL version of the method
        let term = shrinkAst term
        let evaluateTerm = evaluateTerm currentRow
        match term with
        | BinEx(BinOp.Eq, left, UnEx(Like, right)) ->
            let (SqlType.String left) = left |> evaluateTerm
            let (SqlType.String right) = right |> evaluateTerm
            SqlType.Bool (Regex.IsMatch(left, right))
        | BinEx(BinOp.Eq, left, Not(Value(ValueEx.Null))) ->
            let left = evaluateTerm left
            match left with
            | SqlType.Null -> SqlType.Bool false
            | _ -> SqlType.Bool true
        | BinEx(BinOp.Eq, left, Value(ValueEx.Null)) ->
            let left = evaluateTerm left
            match left with
            | SqlType.Null -> SqlType.Bool true
            | _ -> SqlType.Bool false
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
        | Call("CAST", [Cast (term, typ)])
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
                try
                    term.InnerValue
                    |> System.Convert.ToDouble
                    |> SqlType.Float
                with
                | exn -> invalidOp <| sprintf "Unable to cast string %A to float" term.InnerValue
            | "VARCHAR" ->
                term.InnerValue
                |> string
                |> SqlType.String
            //TODO: Implement any other SQL types which might be needed here
            | _ -> term
        | UnEx(Like, _) -> SqlType.Null
        | Call(fnName, arguments) -> SqlType.Null
        | Case(selector, branches, defaultValue) -> 
            let result =
                match selector with
                | Some selector ->
                    let selector = evaluateTerm selector
                    branches
                    |> List.tryFind (fun (v, result) ->
                        let v = evaluateTerm v
                        selector = v)
                | None ->
                    branches
                    |> List.tryFind (fun (v, result) ->
                        let v = evaluateTerm v
                        v = truth)
            match result with
            | Some (_, result) -> evaluateTerm result
            | None -> evaluateTerm defaultValue
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

            interface IExtractor with
                member this.Extract stream =
                    let streamReader = new System.IO.StreamReader(stream)
                    let csvReader = new CsvHelper.CsvReader(streamReader)
                    let headers =
                        csvReader.ReadHeader() |> ignore
                        csvReader.FieldHeaders
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
                    let streamReader = new StreamReader(stream)
                    seq {
                        while not streamReader.EndOfStream do
                            let line = streamReader.ReadLine()
                            let json = JObject.Parse(line)
                            yield collapseJson (json) |> Map.ofList
                     }

        type JsonExtractor(properties:Map<string, string>) =
            interface IExtractor with
                member this.Extract stream =
                    let streamReader = new StreamReader(stream)
                    seq {
                        let content = streamReader.ReadToEnd()
                        let json = JObject.Parse(content)
                        yield collapseJson json |> Map.ofList
                    }

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

        type IWriter = 
            inherit IDisposable
            abstract WriteRecord : Map<string, SqlType> -> unit
            abstract FileExtension : string with get

        type CsvWriter(options:Map<string, string>, stream:Stream) =
            let streamWriter = new StreamWriter(stream)
            let csvHelper = new CsvHelper.CsvWriter(streamWriter)

            interface IWriter with
                member this.Dispose () =
                    (streamWriter :> IDisposable).Dispose()
                member this.FileExtension = "csv"
                member this.WriteRecord fields =
                    let o = System.Dynamic.ExpandoObject()
                    let p = o :> IDictionary<string, obj>
                    fields
                    |> Map.iter (fun k v -> p.Add(k, v))
                    ()

        open Newtonsoft.Json
        open Newtonsoft.Json.Linq

        type JsonLWriter(options:Map<string, string>, stream:Stream) =
            let streamWriter = new StreamWriter(stream)

            let sqlTypeToJObj sqlType =
                match sqlType with
                | SqlType.Null -> JValue.CreateNull()
                | SqlType.Binary bytes -> JValue(bytes)
                | SqlType.Bool b -> JValue b
                | SqlType.Char c -> JValue c
                | SqlType.DateTime dt -> JValue dt
                | SqlType.Float f -> JValue f
                | SqlType.Integer i -> JValue i
                | SqlType.Money m -> JValue m
                | SqlType.String s -> JValue s

            let rec recursivelyTryAddToJObject value (json:JObject) path =
                match path with
                | [x] -> json.Add(x, sqlTypeToJObj value)
                | x::xs ->
                    match json.TryGetValue(x) with
                    | true, v -> 
                        let jo = v :?> JObject
                        recursivelyTryAddToJObject value jo xs
                    | false, _ ->
                        let nestedObject = JObject()
                        recursivelyTryAddToJObject value nestedObject xs
                        json.Add(x, nestedObject)
                | _ -> invalidOp "It's all gone Pete Tong in the JSON writer"

            interface IWriter with
                member this.Dispose() =
                    (streamWriter :> IDisposable).Dispose()
                member this.FileExtension = "jsonl"
                member this.WriteRecord fields =
                    let jobj = Newtonsoft.Json.Linq.JObject()
                    fields
                    |> Seq.iter (fun (KeyValue(key, value)) ->
                        let path = key.Split('.') |> List.ofArray
                        recursivelyTryAddToJObject value jobj path)
                    streamWriter.WriteLine(jobj.ToString(Newtonsoft.Json.Formatting.None))

        let RetrieveWriterByName (name:string) options stream : IWriter = 
            match name.ToLower() with
            | "csv" -> new CsvWriter(options, stream) :> _
            | "jsonl" -> new JsonLWriter(options, stream) :> _
            | _ -> invalidArg "name" "No writer matching that name"

    module Functions =
        let Len str =
            String.length str

        let Char i =
            (char i)