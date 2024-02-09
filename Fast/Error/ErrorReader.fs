(*
    this is a lexer for error messages
    it is used to read error files 

    this is needed to generalize testing
*)
module ErrorReader

open Regex
open Token
open Lexer
open Err
open Position

type Tag =
    | MSG
    | MSGPRE
    | ERROR
    | WHITESPACE
    | ENDING
    | INT
    | LP
    | RP
    | COMMA
    | AT
    | TYPE of ErrorType

let private patterns =
    Lexer([|
        !"lexical", TYPE Lexical
        !"syntax", TYPE Syntax
        !"indentation", TYPE Indentation
        !"TYPE", TYPE Type
        !"eoc", TYPE EOC
        !"(", LP
        !")", RP
        !",", COMMA
        !"error", ERROR
        !"at", AT
        num, INT
        !"\n\n" <|> !"\r\n\r\n", ENDING
        (!":\n\n" <|> !":\r\n\r\n") => !"  " => star !" ", MSGPRE
        plus !" ", WHITESPACE // this allow for illformed errors
        !"\"" => star (letterOrDigit <|> !" ") => !"\"", MSG
    |], [|WHITESPACE|])
    


let ErrorParser tokens =
    let rec loop errs (tokens: Token<Tag> list) =
        match tokens with
        | [] when errs <> [] ->
            List.reduce (fun trailing err -> { err with Trailing = Some trailing }) errs
            |> Ok

        | [] -> Error "no error(s) found"
        // very long pattern of errors 
        | { Type = TYPE ty } :: { Type = ERROR } :: { Type = AT } :: 
            { Type = LP } :: ({ Type = INT } as line) :: { Type = COMMA } :: 
            ({ Type = INT} as offset) :: { Type = RP } ::
            { Type = MSGPRE } :: ({ Type = MSG } as msg) :: { Type = ENDING } :: tokens -> 

            let err = Err.Ty ty msg.Content[1..msg.Content.Length-2] (Pos(int line.Content,int offset.Content, 0))
            loop (err :: errs) tokens

        | _ -> Error "wrongful error format"

    loop [] tokens


let test = "syntax error at (1,2):\n\n  \"error message\"\n\n"

let expect = Ok(Err.Ty Syntax "error message" (Pos(1,2,0))) : Result<Err,string>

let testing =
    let bytes = System.Text.Encoding.ASCII.GetBytes test
    Lexer.TokenList patterns bytes
    |> ErrorParser
    |> (=) expect
    
