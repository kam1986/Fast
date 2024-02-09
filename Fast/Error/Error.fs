module Err

open Position

(*
    A costume error type
    the message are the error message cast at that point
    with position info.
    the Trailing is used to capture error sequences
    i.e. if an error happens because of another error

    this is important since it will give a more detailed information
    for the user, and for us while writing the compiler.

    it is a struct since it is small and it eleminiate double reference in the trailing part
*)
[<Struct>]
type Err =
    {
        Type: ErrorType
        Message: string
        Position: Pos
        Trailing: Err option
    }
with
    override E.ToString() =
        let trailing = 
            Option.map string E.Trailing
            |> Option.defaultValue "\n"

        // easy to parse 
        $"{E.Type.ToString().ToLower()} error at {E.Position}:\n\n  \"{E.Message}\"\n\n{trailing}"


// we use tags instead of DUs
// since the feilds are the same
// and it leads to less branching code
//
// it is important to know when to use which type.
and [<Struct>] ErrorType =
    | Lexical
    | Syntax
    | Indentation
    | Type
    | EOC



module Err =
    // create a costume error type
    // used in each module of the compiler 
    // to reuse common patterns of creation
    let inline internal Ty ty msg pos =
        { 
            Type = ty
            Message = msg
            Position = GetPos pos
            Trailing = None
        }

    let inline Lexical msg pos =
        Ty Lexical msg pos
        |> Error

    let inline Syntax msg pos =
        Ty Syntax msg pos
        |> Error

    let inline Indentation msg pos =
        Ty Indentation msg pos
        |> Error

    let inline Type msg pos =
        Ty Type msg pos
        |> Error

    let inline EOC pos =
        Ty EOC "unexpectedly reach end of context" pos
        |> Error

    // Add an error as trailing error
    // to an existing error.
    let Add trailing err = { err with Trailing = Some trailing }
    
    // print error with trailing error information
    let PrintAll err =
        let rec printer err =
            printfn $"{err.Type}: {err.Message} at {err.Position}"
            Option.iter (fun err -> 
                printfn "\nresulted from\n"
                printer err) err.Trailing

        printer err
    
    // print top most error information
    let Print err =  printfn $"{err.Type}: {err.Message} at {err.Position}"
    
    // error catcher used to 
    // handle error in different ways
    // f.x. in debug mode, it will read code files
    // write results to other files, and test them against files with expected output
    // and print an error if it occurs. the 'Log' function will be used both as the file writer
    // and as the printer. this way we can use a logger function as argument at top level instead of
    // rewriting a lot of code or handling special cases.
    let Log logger (err: Err): unit =
        logger err
       
    // same as above but with result
    let LogWithResult logger err ret =
        Log logger err
        ret

