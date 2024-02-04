
open Lexing
open Parsing
// For more information see https://aka.ms/fsharp-console-apps
printfn "Hello from Fast"
printfn ""
printfn "this is a language ment to be the level just between C/rust and assembly"
printfn "it has more structure than assembly, but less types and safty than C"
printfn "it is also ment as an intermediate to other languages"
printfn "the point of Fast is to make memory management and pointer handling more codeable with less bugs"
printfn ""

let text = 
    "##\nthis is a while loop\n##\nwhile true\ndo\n  answer <- 42"

text
|> Lex
|> Result.mapError (fun err -> ())
|> Result.map ParseStmt
|> Result.mapError (fun err -> ())
|> Result.iter (printfn "%A")

