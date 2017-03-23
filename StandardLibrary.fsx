module StdLib =
    module Extractors =
        open System.IO
        // open Sql.Ast

        // type Schema = {
        //     SchemaName : string
        //     Columns : (string * ValueEx) array
        // }

        type IExtractor = interface end
        // type IBinaryExtractor =
        //     inherit IExtractor
        //     abstract member Extract : Stream -> seq<Map<string, ValueEx>>
        // type ITextExtractor =
        //     inherit IExtractor
        //     abstract member Extract : string -> seq<Map<string, ValueEx>>
        // type ILineExtractor =
        //     inherit IExtractor
        //     abstract member Extract : Schema -> string -> Map<string, ValueEx>
        // type IHeaderBasedExtractor =
        //     inherit ILineExtractor
        //     abstract member ParseHeaders : string -> string []

        let RetrieveExtractorByName name =
            { new IExtractor }

    module Writers =
        open System.IO
        // open Sql.Ast

        type IWriter = interface end

    module Functions =
        let Len str =
            String.length str

        let Char i =
            (char i)