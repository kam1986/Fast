namespace TestLPI

open System
open Microsoft.VisualStudio.TestTools.UnitTesting

open Regex

[<TestClass>]
type TestClass () =

    [<TestMethod>]
    member this.TestAll () =
        Regex.RegexTest()