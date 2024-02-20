module Lexing

open Err
open Lexer
open Regex

type Tag =
    | ID
    | NUMBER
    | UINT8
    | UINT16
    | UINT32
    | UINT64
    | SINT8
    | SINT16
    | SINT32
    | SINT64
    | FLOAT32
    | FLOAT64
    | FLOAT128
    | PLUS
    | MINUS
    | SLASH
    | STAR
    | NOT
    | TRUE
    | FALSE
    | SEMICOLON
    | LZ // leading zeros
    | TZ // trailing zeros
    | BC // bit count
    | XOR
    | OR
    | AND
    | LAND
    | LOR
    | IMPLY
    | LE
    | GE
    | GT
    | LT
    | EQ
    | NE
    | LR
    | RR
    | LS
    | RS
    | REM
    | ARROW
    | LPARANT
    | RPARANT
    | CONTINUE
    | BREAK
    | RETURN
    | COMMA
    | CEIL
    | FLOOR
    | SQRT
    | ROUND
    | LET
    | MUT
    | FUN
    | IF
    | WHEN
    | WHILE
    | ELSE
    | THEN
    | DO
    | S8
    | S16
    | S32
    | S64
    | U8
    | U16
    | U32
    | U64
    | F32
    | F64
    | F128
    | DEREF
    | MODULE
    | WS // whitespace
    | SINGLELINECOMMENT
    | MULTILINECOMMENT

let id = letter => star letterOrDigit
let whitespace = plus (!" " <|> !"\n" <|> !"\r")

let symbols = "!\"@#£¤$%&€/{([)]=}?`|´~^¨',.-;:_<\\>"


let AnyOf chars = 
    Seq.map (fun char -> !($"{byte char}")) chars
    |> Seq.reduce (<|>)

(*
    a singleline comment is a printable ascii sequence that is not a \r or \n starting with
    // and ending in either a unix or windows linebreak
*)
let singleline = !"//" => star (letter <|> digit <|> !" " <|> AnyOf symbols) => (!"\n" <|> !"\r\n")

(*
    a multipline comment are a sequence of printable ascii characters
    starting and ending with ##, where # may not occur 
*) 
let multiline = 
    let symbols = (AnyOf << Seq.filter (fun c -> c <> '#')) symbols
    !"##" => star (whitespace <|> id <|> symbols) => !"##"


let private lexer =
    Lexer([|        
        !"+", PLUS
        !"-", MINUS
        !"/", SLASH
        !"*", STAR
        !"%", REM
        !"&", AND
        !"|", OR
        !"^", XOR
        !"not", NOT
        !"#", DEREF
        !"<<", LS
        !">>", RS
        !"<o", LR
        !"o>", RR
        !"&&", LAND
        !"||", LOR
        !"->", IMPLY
        !"lz", LZ
        !"tz", TZ
        !"bc", BC 
        !"<", LE
        !"<=", LT
        !">=", GT
        !">", GE
        !"=", EQ
        !"<>", NE
        !"<-", ARROW
        !"(", LPARANT
        !")", RPARANT
        !",", COMMA
        !";", SEMICOLON

        !"s8",   S8
        !"s16",  S16
        !"s32",  S32
        !"s64",  S64
        !"u8",   U8
        !"u16",  U16
        !"u32",  U32
        !"u64",  U64
        !"f32",  F32
        !"f64",  F64
        !"f128", F128

        !"let", LET
        !"true", TRUE
        !"false", FALSE
        !"mut", MUT
        !"fun", FUN
        !"break", BREAK
        !"continue", CONTINUE
        !"return", RETURN
        !"module", MODULE
        !"when", WHEN
        !"else", ELSE
        !"if", IF
        !"while", WHILE
        !"then", THEN
        !"do", DO
        num => !"uy", UINT8
        num => !"us", UINT16
        num => !"u", UINT32
        num => !"ul", UINT64
        
        snum => !"y", SINT8
        snum => !"s", SINT16
        snum, SINT32
        snum => !"l", SINT64

        floating, FLOAT64
        floating => !"f", FLOAT32
        floating => !"d", FLOAT128

        id, ID
        whitespace, WS
        singleline, SINGLELINECOMMENT
        multiline, MULTILINECOMMENT
    |], [|WS; SINGLELINECOMMENT; MULTILINECOMMENT|])
    

let Lex (input: string) =
    try
        input
        |> System.Text.Encoding.ASCII.GetBytes
        |> TokenList lexer 
        |> Ok
    with LexErr(msg, pos) -> Err.Lexical msg pos
           