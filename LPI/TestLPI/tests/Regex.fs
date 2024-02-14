module Regex
open System
open Microsoft.VisualStudio.TestTools.UnitTesting
open Regex

[<TestClass>]
type RegexTest() =
    
    [<TestMethod>]
    member _.TestAssignPosition () =
        let actual =
            [
                !"a"
                !"a" => !"b"
                !"a" <|> !"b"
                star (!"a" => !"b")
                Terminal -1
                Epsilon
            ]
            |> List.map AssignPosition
            |> List.map fst

        let expected =
            [
                Atom(byte 'a', 0)
                Cat(Atom(byte 'a',0),Atom(byte 'b', 1), set[0], set[1], false)
                Or(Atom(byte 'a',0),Atom(byte 'b',1), set[0;1], set[0;1], false)
                Terminal -1
                Epsilon
            ]

        actual = expected
        |> Assert.IsTrue