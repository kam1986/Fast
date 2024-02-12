
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

// used to apply testing
#if DEBUG 
open ErrorReader
open Ast
open Type
open Table

(*
    TODO:
        implement for all folders in Tests do for all files in each folder do
        run test

        because this makes testing easier.
*)
testing 
|> printfn "the error parser runs fine: %A"

let test = "fun add(x, y)\n  return x + y"


test
|> Lex
|> Result.bind ParseModule
|> Result.mapError (printfn "%A")
|> Result.iter (printfn "%A")



#else


#endif