module Testing

open System
open System.Text
open System.IO




let StartTest code =
    let codeInfo = FileInfo code
    let folderinfo = 
        DirectoryInfo $"./Tests/{codeInfo.Name[..codeInfo.Name.Length - 1 - codeInfo.Extension.Length]}"
    
    let tests =    
        Directory.CreateDirectory($"{folderinfo.FullName}/Tests")

    let exp =
        Directory.CreateDirectory($"{folderinfo.FullName}/Expects")

    let ret =
        Directory.CreateDirectory($"{folderinfo.FullName}/Results")

    let run =
        let rets =
            ret.GetFiles()
            |> Array.map (fun file -> file.LastWriteTime)
            |> Array.forall (fun updated -> updated < codeInfo.LastWriteTime)

        let tests =
            tests.GetFiles()
            |> Array.map (fun file -> file.LastWriteTime)
            |> Array.exists (fun updated -> updated > codeInfo.LastWriteTime)
            
        rets || tests


    if run then
        printfn $"Running tests for {codeInfo.Name}"
        printfn "\n"
        
    




(*
    get base directory

    in base directory

        Directory
            Tests
                testfiles..

            Expected
                testfile.err/ok

            Results
                results.err
                results.ok
            


*)