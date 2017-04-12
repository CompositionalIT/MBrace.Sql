#r """packages/FParsec/lib/net40-client/FParsecCS.dll"""
#r """packages/FParsec/lib/net40-client/FParsec.dll"""

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
        "END"; "IS"; "NULL"; "TRUE"; "FALSE"; "USING"; "EXTRACTOR"; "WRITER"; "INTO"
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
            spaces >>. ((between_str "("  ")" expr) <|> (between_str "("  ")" sqlParser) <|> sqlParser <|> expr) .>> spaces
            
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
        opp.AddOperator(InfixOperator("<>", spaces, 1, Assoc.None, (fun x y -> Not(BinEx(BinOp.Eq, x, y)))))

        opp.AddOperator(InfixOperator("AND", notFollowedBy letter >>. spaces, 2, Assoc.None, (fun x y -> And(x,y))))
        opp.AddOperator(InfixOperator("OR", notFollowedBy letter >>. spaces, 2, Assoc.None, (fun x y -> Or(x,y))))

        
        expr <|> between_str "(" ")" expr

    
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
        choice [ fileSource; resultSet;  (alias |>> OriginEx.ResultSet) ]

    let destination =
        let resultSet =
            pchar '#' >>. identifier |>> (fun id -> DestinationEx.ResultSet(id))
        let fileSource =
            let extractor = keyword "USING" >>. keyword "WRITER" >>. identifier |>> fun id -> WriterEx.Writer(id)
            let parser = quotedStr .>>. extractor
            parser |>> DestinationEx.Folder
        fileSource <|> resultSet
    

    let destinationEx =
        keyword "INTO" >>.
        destination

    let aliasedOrigin =
        let t = (fileOrigin .>>. (opt (attempt alias)))
        spaces >>. t .>> spaces

    let fromEx =
        keyword "FROM" >>. aliasedOrigin |>> From

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