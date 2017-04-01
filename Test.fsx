#load """packages/testing/MBrace.Azure/MBrace.Azure.fsx"""
#r """packages/MBrace.Core/lib/net45/MBrace.Core.dll"""
#load """SqlTranspiler.fsx"""

open SqlParser.Ast
open SqlTranspiler.Transpiler
open StandardLibrary.StdLib
open StandardLibrary
open StandardLibrary.StdLib.Extractors

let storageConnectionString = """DefaultEndpointsProtocol=https;AccountName=mbstorage6nvf6tq7stxnm;AccountKey=gKZkgNlCsQ+nBxs7rJxlvNCYD8/aj8yblXjOHRPKMDTQktSpsDW0WNvoJ+kPkdR4EPdntMUC2x77+7Vuyz9whg=="""
let serviceBusConnectionString = """Endpoint=sb://mbmsg6nvf6tq7stxnm.servicebus.windows.net/;SharedAccessKeyName=RootManageSharedAccessKey;SharedAccessKey=WzWghvlsw+vsRHYji3OzlaFiGFORhR+pco2ub/K0rHg="""

let orTest = TermEx.Or(TermEx.Value(ValueEx.Bool(false)), TermEx.Value(ValueEx.Bool(true)))
let andTest = TermEx.And(TermEx.Value(ValueEx.Bool(true)), TermEx.Value(ValueEx.Bool(true)))
let addTest = TermEx.BinEx(BinOp.Add, TermEx.Value(ValueEx.Integer(5)), TermEx.Value(ValueEx.Integer(7)))
let refAddTest = TermEx.BinEx(BinOp.Add, TermEx.Ref(["user"; "likecount"]), TermEx.Ref(["user"; "retweetcount"]))
let regexTest = BinEx(BinOp.Eq, Value(ValueEx.String "bruinbrown"), UnEx(Like, Value(ValueEx.String "bruin.*")))
let equalityTest = BinEx(BinOp.Eq, Value(ValueEx.Bool true), Value(ValueEx.Bool true))
let castTest = Cast(Value(ValueEx.Integer 5), "VARCHAR")
let userTwitterData = ["user.likecount", SqlType.Integer 27; "user.retweetcount", SqlType.Integer 32; "user.username", SqlType.String "bruinbrown"] |> Map.ofList

let result = evaluateTerm userTwitterData andTest

open MBrace.Core
let cluster = MBrace.Azure.AzureCluster.Connect(storageConnectionString, serviceBusConnectionString)
let parsed = SqlParser.Parser.parse "SELECT 'Hello World' AS Greeting, [user].[username], [user].[age] FROM 'test/TwitterData.jsonl' USING EXTRACTOR JSONL WHERE user.age > 20 INTO #output"

let secondQuery = SqlParser.Parser.parse "SELECT * FROM #output"

cluster.Store.CloudFileSystem.Store.UploadFromLocalFile("""C:\Users\bruin\Downloads\test.jsonl""", "test/TwitterData.jsonl") |> Async.RunSynchronously

cluster.Store.CloudFileSystem.Store.EnumerateFiles("") |> Async.RunSynchronously

open MBrace.Flow
let a : CloudDictionary<PersistedCloudFlow<Map<string, SqlType>>> = cluster.Store.CloudDictionary.New("MBraceSqlResults")
a.Dispose() |> Async.RunSynchronously
match parsed with
| TermEx.QueryEx query -> cluster.Run(TranspileSqlAstToCloudFlow query)
| _ -> invalidOp ""

match secondQuery with
| TermEx.QueryEx query -> cluster.Run(TranspileSqlAstToCloudFlow query)
| _ -> invalidOp ""

a.TryFind("output")
a.Remove("output")
