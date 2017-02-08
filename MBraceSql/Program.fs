// Learn more about F# at http://fsharp.net
// See the 'F# Tutorial' project for more help.

module Sql =
    
    open FParsec
    open FParsec.Primitives
    open FParsec.CharParsers
    open System.Collections.Generic

    module Ast =
        module Str = String

        type BinOp =
            | Gt | Lt | Gte | Lte | Eq
            | Add | Mul | Div | Sub | Mod

         type UnOp =
            | Like | Neg           

        type JoinDir =
            | Left | Right
        
        type JoinType =
            | Inner | Outer | Full | Cross
        
        type OrderDir =
            | ASC | DESC

        type ValueEx =
            | String of string
            | Float of float
            | Integer of int
            | Bool of bool
            | Null
            member this.InnerValue =
                match this with
                | String v -> box v
                | Float v -> box v
                | Integer v -> box v
                | Bool v -> box v
                | Null -> null
            static member (~-) v =
                match v with
                | Float v -> Float (-v)
                | Integer v -> Integer(-v)
                | _ -> invalidOp "The type does not support the - operator"

            static member (+) (left, right) =
                match left, right with
                | Float f1, Float f2 -> Float(f1 + f2)
                | Integer i1, Integer i2 -> Integer(i1 + i2)
                | _, _ -> invalidOp "Types don't match"

            static member (-) (left, right) =
                match left, right with
                | Integer i1, Integer i2 -> Integer(i1 - i2)
                | Float f1, Float f2 -> Float(f1 - f2)
                | _, _ -> invalidOp "Types don't match"

            static member (/) (left, right) =
                match left, right with
                | Integer i1, Integer i2 -> Integer(i1 / i2)
                | Float f1, Float f2 -> Float(f1 / f2)
                | _, _ -> invalidOp "Types don't match"

            static member (*) (left, right) =
                match left, right with
                | Integer i1, Integer i2 -> Integer(i1 * i2)
                | Float f1, Float f2 -> Float(f1 * f2)
                | _ -> invalidOp "Types don't match"

            static member (%) (left, right) =
                match left, right with
                | Integer i1, Integer i2 -> Integer(i1 % i2)
                | _ -> invalidOp "Types don't match"
            
        type OrderEx =
            | Order of string * OrderDir option
        
        type TermEx =
            | BinEx of (BinOp * TermEx * TermEx)
            | And of TermEx * TermEx
            | Or of TermEx * TermEx
            | Not of TermEx
            | UnEx of UnOp * TermEx
            | Value of ValueEx
            | Ref of string list
            | Cast of TermEx * string
            | Call of string * TermEx list
            | Case of TermEx option * (TermEx * TermEx) list * TermEx
            | QueryEx of Query
            
        and ProjectionEx =
            | Projection of TermEx * string option
            | Distinct of ProjectionEx list
            | Top of int * ProjectionEx list

        and JoinEx =
            | Join of (JoinDir option * JoinType) * (TermEx * string option) * TermEx
        
        and ExtractorEx =
            | Extractor of string

        and WriterEx =
            | Writer of string

        and OriginEx =
            | ResultSet of string
            | DataSource of string * ExtractorEx

        and FromEx =
            | From of (OriginEx * string option) 

        and GroupByEx =
            | Group of TermEx * string option

        and DestinationEx =
            | ResultSet of string
            | Folder of string * WriterEx
                    
        and Query = {
            Projection : ProjectionEx list
            Filters : TermEx option
            Order : OrderEx list option
            Join : JoinEx list
            From : FromEx
            GroupBy : GroupByEx list option
            Destination : DestinationEx option
        }

        type Assoc = Associativity
        
    module Parser =

        open System
        open Ast

        let symbols = "[]\"'()*,.".ToCharArray()
        let quote = skipStringCI "\"" <|> skipStringCI "'"
        let identifierString = many1Satisfy (fun c -> not(System.Char.IsWhiteSpace c) && isNoneOf symbols c)

        let keywords = [
            "SELECT"; "FROM"; "WHERE"; "JOIN"; "AS"; "GROUP"; "ORDER"; "HAVING"
            "BY"; "INNER"; "OUTER"; "LEFT"; "RIGHT"; "FULL"; "CROSS"; "ON"; "ASC"; "DESC";
            "AND"; "OR"; "NOT"; "LIKE"; "ORDER BY"; "DISTINCT"; "TOP"; "CASE"; "WHEN"; "THEN";
            "END"; "IS"; "NULL"; "TRUE"; "FALSE"; "USING"; "EXTRACTOR"; "WRITER";
        ]
        
        let str_ws s = pstring s .>> spaces
        let str_ws1 s = pstring s .>> spaces1
        let between_str a b p = between (str_ws a) (str_ws b) p 
        
        let keywordSet = new HashSet<string>(keywords)
        let isKeyword (kw:string) = keywordSet.Contains(kw.ToUpper())
        
        let keyword (kw:string) = 
            spaces >>. skipStringCI kw >>. spaces
            
        let identifier : Parser<string, unit> =
            let expectedIdentifier = expected "identifier"
            fun stream ->
                let state = stream.State
                let reply = identifierString stream
                if reply.Status = Ok && not(isKeyword reply.Result) 
                then reply
                else // result is keyword, so backtrack to before the string
                    stream.BacktrackTo(state)
                    Reply(Error, expectedIdentifier)
        
        let quotedStr = ((skipChar 'N' >>.  quote) <|> quote) >>. manyCharsTill anyChar quote

        let strLiteral = quotedStr |>> Ast.String
        
        let numberLiteral =
            (pint32 |>> Ast.Integer) <|> (pfloat |>> Ast.Float)

        let nullLiteral = keyword "NULL" >>% Null

        let boolLiteral =
            choice [
                keyword "TRUE" |>> (fun _ -> Bool true)
                keyword "FALSE" |>> (fun _ -> Bool false)
            ]
                
        let primitiveLiteral =
            choice [
                nullLiteral
                boolLiteral
                strLiteral
                numberLiteral
            ]

        let primitiveEx =
            spaces >>. primitiveLiteral .>> spaces
            |>> Value
            
        let alias =
            spaces >>. (
              (keyword "AS" >>. (quotedStr <|> identifier <|> (between_str "["  "]" identifier)))
              <|>
              (quotedStr <|> identifier) 
            ) .>> spaces
        
        let reference =
            let r = 
                spaces >>.
                sepBy1 ((pstring "*")
                        <|> identifier
                        <|> (between_str "[" "]" identifier)
                       ) (pchar '.')
                .>> spaces
                |>> Ref
            between_str "(" ")" r
            <|>
            r
                
        let (sqlParser, sqlParserRef) = createParserForwardedToRef()
                
        let termEx =
            let opp = new OperatorPrecedenceParser<Ast.TermEx, unit, unit>()
            let expr = opp.ExpressionParser
            let term =
                spaces >>. ((between_str "("  ")" expr) <|> (between_str "("  ")" sqlParser) <|> sqlParser) .>> spaces
                
            opp.TermParser <- term

            opp.AddOperator(PrefixOperator("-", spaces, 1, true, (fun x -> UnEx(UnOp.Neg, x))))
            opp.AddOperator(PrefixOperator("NOT", notFollowedBy letter >>. spaces, 1, true, (fun x -> Not(x))))
            opp.AddOperator(PrefixOperator("LIKE", notFollowedBy letter >>. spaces, 1, true, (fun x -> UnEx(UnOp.Like, x))))

            opp.AddOperator(InfixOperator("*", spaces, 1, Assoc.Left, (fun x y -> BinEx(BinOp.Mul, x, y))))
            opp.AddOperator(InfixOperator("/", spaces, 1, Assoc.Left, (fun x y -> BinEx(BinOp.Div, x, y))))
            opp.AddOperator(InfixOperator("+", spaces, 1, Assoc.Left, (fun x y -> BinEx(BinOp.Add, x, y))))
            opp.AddOperator(InfixOperator("-", spaces, 1, Assoc.Left, (fun x y -> BinEx(BinOp.Sub, x, y))))
            opp.AddOperator(InfixOperator("%", spaces, 1, Assoc.Left, (fun x y -> BinEx(BinOp.Mod, x, y))))
        
            opp.AddOperator(InfixOperator("IS", notFollowedBy letter >>. spaces, 2, Assoc.None, (fun x y -> BinEx(BinOp.Eq, x, y))))  
            opp.AddOperator(InfixOperator("=", spaces, 1, Assoc.None, (fun x y -> BinEx(BinOp.Eq, x, y))))
            opp.AddOperator(InfixOperator("<", spaces, 1, Assoc.None, (fun x y -> BinEx(BinOp.Lt, x, y))))
            opp.AddOperator(InfixOperator(">", spaces, 1, Assoc.None, (fun x y -> BinEx(BinOp.Gt, x, y))))
            opp.AddOperator(InfixOperator("<=", spaces, 1, Assoc.None, (fun x y -> BinEx(BinOp.Lte, x, y))))
            opp.AddOperator(InfixOperator(">=", spaces, 1, Assoc.None, (fun x y -> BinEx(BinOp.Gte, x, y))))

            opp.AddOperator(InfixOperator("AND", notFollowedBy letter >>. spaces, 1, Assoc.Left, (fun x y -> And(x,y))))
            opp.AddOperator(InfixOperator("OR", notFollowedBy letter >>. spaces, 1, Assoc.Left, (fun x y -> Or(x,y))))

            between_str "(" ")" expr
            <|>
            expr

        
        let aliasedTermEx =
            let t = (termEx .>>. (opt (attempt alias)))
            spaces >>. t .>> spaces
            
        let termOrCastEx =
            let cast =
                attempt (opt (keyword "AS" >>.  identifier))
            spaces >>. termEx .>> spaces .>>. cast .>> spaces
            |>> function
                | a, None -> a
                | a, Some b -> Cast(a, b)

        let caseEx =
            let cases =
                manyTill (keyword "WHEN" >>. (termOrCastEx <|> termEx)
                          .>> keyword "THEN"
                           .>>. (termOrCastEx <|> termEx)
                          ) (keyword "ELSE") 
                .>>.  (termOrCastEx <|> termEx) .>> keyword "END"
               
            keyword "CASE" >>. (attempt (opt termEx)) .>>. cases
            |>> (fun (cond, (cases, terminal)) -> Case(cond, cases, terminal))

        let callEx =
            identifier .>>. between_str "(" ")" (sepBy (termOrCastEx <|> termEx) (pstring ","))
            |>> Call
        
        let selectEx =
            let projections =
                sepBy1 (aliasedTermEx |>> Projection) (pstring ",")    
            
            let modifiers =
                choice [
                    keyword "DISTINCT" >>. projections |>> fun x -> [Distinct x]
                    keyword "TOP" >>. pint32 .>> spaces .>>. projections |>> (fun (i, ps) ->  [Top(i, ps)])
                    projections
                ]
            
            keyword "SELECT" >>. modifiers
           
        let fileOrigin =
            let resultSet =
                pchar '#' >>. identifier |>> (fun id -> OriginEx.ResultSet(id))
            let fileSource =
                let extractor = keyword "USING" >>. keyword "EXTRACTOR" >>. identifier |>> fun id -> ExtractorEx.Extractor(id)
                let parser = quotedStr .>>. extractor
                parser |>> OriginEx.DataSource
            let origin =
                choice [ fileSource; resultSet ]
            origin

        let destination =
            let resultSet =
                pchar '#' >>. identifier |>> (fun id -> DestinationEx.ResultSet(id))
            let fileSource =
                let extractor = keyword "USING" >>. keyword "WRITER" >>. identifier |>> fun id -> WriterEx.Writer(id)
                let parser = quotedStr .>>. extractor
                parser |>> DestinationEx.Folder
            let origin =
                choice [ fileSource; resultSet ]
            origin

        let destinationEx =
            keyword "INTO" >>.
            destination

        let aliasedOrigin =
            let t = (fileOrigin .>>. (opt (attempt alias)))
            spaces >>. t .>> spaces

        let fromEx =
            keyword "FROM" >>.
            aliasedOrigin |>> From

        let whereEx = keyword "WHERE" >>. termEx

        let joinEx =
            let joinDir =
                spaces
                >>. (attempt (opt
                        (choice [
                                    keyword "LEFT" >>% JoinDir.Left
                                    keyword "RIGHT" >>% JoinDir.Right
                                ])))
                .>> spaces
            
            let joinType =
                spaces >>. choice [
                        keyword "JOIN" >>% JoinType.Inner
                        keyword "INNER JOIN" >>% JoinType.Inner
                        keyword "OUTER JOIN" >>% JoinType.Outer
                        keyword "FULL JOIN" >>% JoinType.Full
                        keyword "CROSS JOIN" >>% JoinType.Cross
                ] .>> spaces

            let joinClass =
                (joinDir .>>. joinType)
            
            let join =
                (joinClass .>>. aliasedTermEx .>> keyword "ON" .>>. termEx)
                |>> (fun ((x,y),z) -> Join(x,y,z))
        
            manyTill join (notFollowedBy joinClass)

        let groupByEx =
            keyword "GROUP BY" >>. sepBy1 (aliasedTermEx |>> Group) (pstring ",")    
        
        let orderEx =
            let direction = 
                opt (
                      ((keyword "ASC") >>% OrderDir.ASC)
                       <|>
                      ((keyword "DESC") >>% OrderDir.DESC)
                )
            
            let ids = 
                (spaces >>. (identifier .>>. attempt (spaces >>. direction .>> spaces)))

            keyword "ORDER BY" >>. (sepBy ids (pstring ","))
            |>> List.map OrderEx.Order

        let queryEx =
            parse {
                let! select = selectEx
                let! from = fromEx
                let! join = attempt joinEx
                let! where = attempt (opt whereEx)
                let! group = attempt (opt groupByEx)
                let! order = attempt (opt orderEx)
                let! destination = attempt (opt destinationEx)
                return {
                   Projection = select
                   Filters = where
                   Order = order
                   Join = join
                   From = from
                   GroupBy = group
                   Destination = destination
                }
            } |>> QueryEx
            
        do
           sqlParserRef :=
                choice [
                    attempt callEx
                    primitiveEx
                    reference
                    caseEx
                    queryEx
                ]
        
        let parse (str:string) =
            match run sqlParser (str.Trim()) with
            | Success(r,_,_) -> r
            | Failure(msg, err,_) -> failwithf "Failed to parse %s'" msg

module StdLib =
    module Extractors =
        open System.IO
        open Sql.Ast

        type Schema = {
            SchemaName : string
            Columns : (string * ValueEx) array
        }

        type IExtractor = interface end
        type IBinaryExtractor =
            inherit IExtractor
            abstract member Extract : Stream -> seq<Map<string, ValueEx>>
        type ITextExtractor =
            inherit IExtractor
            abstract member Extract : string -> seq<Map<string, ValueEx>>
        type ILineExtractor =
            inherit IExtractor
            abstract member Extract : Schema -> string -> Map<string, ValueEx>
        type IHeaderBasedExtractor =
            inherit ILineExtractor
            abstract member ParseHeaders : string -> string []

        let RetrieveExtractorByName name =
            { new IExtractor }

    module Writers =
        open System.IO
        open Sql.Ast

        type IWriter = interface end

    module Functions =
        let Len str =
            String.length str

        let Char i =
            (char i)

module Transpiler =
    module Str = String

    open Sql.Ast
    open MBrace.Flow
    open MBrace.Core
    open StdLib.Extractors
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
            let left = left |> evaluateTerm |> string
            let right = right |> evaluateTerm |> string
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
                let! d = MBrace.Core.CloudDictionary.GetById<PersistedCloudFlow<Map<string, SqlType>>>("__MBrace.Sql.Results")
                let! cf = d.TryFindAsync(rsName) |> Cloud.OfAsync
                let cf =
                    cf
                    |> Option.map (fun t -> t :> CloudFlow<Map<string, SqlType>>)
                return cf
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

    let rec private buildProjections (cloudFlow:CloudFlow<Map<string, SqlType>>) (projections:ProjectionEx list) =
        let applyProjectionToRow (projections:ProjectionEx list) (row:Map<string, SqlType>) =
            projections
            |> List.fold (fun s t ->
                let (Projection(term, alias)) = t //I honestly can't remember why I did this, I think it's because a table or column reference can be computed in SQL e.g. SELECT * FROM ("Table" + "A")
                let (SqlType.String(str)) = evaluateTerm row term
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
            let apply = applyProjectionToRow projections
            cloudFlow
            |> CloudFlow.map apply

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

[<AutoOpen>]
module CloudClientExtensions =
    open MBrace.Core
    open MBrace.Runtime
    open Transpiler
    open Sql
    open Sql.Ast

    type MBrace.Runtime.MBraceClient with
        member this.ExecuteSql(sql:string) =
            let res = Sql.Parser.parse sql
            let clo =
                match res with
                | QueryEx q -> TranspileSqlAstToCloudFlow q
                //TODO: Some of the other SQL types we'll have in here are DROP and CREATE TABLE etc
                //TODO: The output also needs changing to reflect whether we're returning a vector, scalar or non query
                | _ -> failwith "Unsupported query type used"
            this.Run(clo)

module Program =
    open MBrace.Flow
    open MBrace.Runtime

    [<EntryPoint>]
    let main argv = 
        let cf = CloudFlow.OfArray([| "Header1, Header2, Header3"; "0.5, Test Name, 0.6" |])
        let mbraceClient = Unchecked.defaultof<MBraceClient>
        let output = mbraceClient.ExecuteSql("")
        0 // return an integer exit code