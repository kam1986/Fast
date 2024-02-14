(*
    TODO: alter the lexer to instead of taking a tag as token type
    instead give it a function taking a content as a byte array and the start and end position
    returning a value of type 'token

    it would make it much more flexible to interop with other code.

    example

    type token =
        | Add of pos * pos
        | Sub of pos * pos
        | I32 of int * pos * pos

    Lexer [|
        !"+", (fun content startpos endpos -> Add(startpos, endpos)) 
        !"-", (fun content startpos endpos -> Sub(startpos, endpos))
        integer, (fun content startpos endpos -> I32(AsInt content, startpos, endpos))
    |]
*)
module Lexer

open Position
open Regex
open DFA
open Token

[<Struct>]
type LexerResult<'t> =
     | EOF
     | Ret of token: (Token<'t> * byte seq)
     | LexError of msg: string * Pos
with
    override ret.ToString() =
        match ret with
        | EOF -> "eof"
        | Ret (token, _) -> string token
        | LexError (msg, pos) -> $"lexer error:\n  {msg} at {pos}"

exception LexErr of string * Pos


/// this a lexer type based on deterministic finite automata
/// it pattern match at byte size which makes it able to parse all classes of character classes
/// it takes an array of regex patterns and a token type tag (either a enum or DU) and an optional
/// array of tokens the user wish to filter out like filter
/// the lexer can be used as argument in concurrent programming
/// since the "state" are wrapped inside the functions and not the lexer itself.
/// it do no code generation hence can be modified and created at runtime
/// the precedence of expression goes from front to back, hence a pattern appearing before another
/// will overrule on return for a token matching the samme pattern
///
/// the whole lexer instance should not exceed 74752 bytes + array for token type tags
type Lexer<'token>  =
    val dfa: DFATable
    val filter: 'token[] option
    val tokens: 'token array
    new (patterns : (Regex * 'token) array, ?filter) =
        let regexs, tokens = Array.unzip patterns
        let regex =
            regexs
            |> Array.mapi (fun i regex -> regex => Terminal (-(i+1)))
            |> Array.fold (fun regex reg -> reg <|> regex) Epsilon
            |> AssignPosition

             
        let dfa = Construct regex
        { dfa = dfa; tokens = tokens; filter = filter }


/// strictly find next token, erroring if no token are match in front of the current codepoint
let rec NextToken (lexer: Lexer<'token>) pos src' =
    // inefficient way to get the utf8 str of the bytes
    let inline content (bytes: byte list) = 
        bytes 
        |> Array.ofList
        |> Array.rev
        |> System.Text.Encoding.UTF8.GetString

    let rec loop pos' acc state src' =
        if Seq.isEmpty src' then
            if state = 0 then EOF
            else
            match lexer.dfa.terminals[state] with
            | -1 -> LexError ("illegal pattern", pos)
            | t -> 
                match lexer.filter with
                | None -> 
                    (Token(lexer.tokens[t], pos, Move pos' -1, content acc), src') 
                    |> Ret
                
                | Some wp when not(Array.contains lexer.tokens[t] wp) -> 
                    (Token(lexer.tokens[t], pos, Move pos' -1, content acc), src')
                    |> Ret

                | _ -> EOF
        else
            let symbol = Seq.head src'
            match lexer.dfa[state, int symbol] with
            | -1 ->
                match lexer.dfa.terminals[state] with
                | -1 -> LexError ("illegal pattern", pos)
                | t ->
                    match lexer.filter with
                    | None -> (Token(lexer.tokens[t], pos, Move pos' -1, content acc), src') |> Ret
                    | Some wp when not(Array.contains lexer.tokens[t] wp) -> 
                        (Token(lexer.tokens[t], pos, Move pos' -1, content acc), src') 
                        |> Ret
                    | _ -> NextToken lexer pos' src'
            | state -> 
                let pos' = if symbol = byte '\n' then NewLine pos' else Next pos'
                loop pos' (symbol :: acc) state  (Seq.tail src')

    loop pos [] 0 src'



// strictly lex the whole source code
let Tokens lexer src =
    let mutable tokens = ResizeArray(Seq.length src >>> 3) // len / 8 as a qualified guees of number of tokens 
    let rec loop pos src' =
        match NextToken lexer pos src' with
        | EOF -> tokens
        | Ret(token, rest) ->
            tokens.Add token
            loop (Move token.End 1) rest

        | err -> failwith (err.ToString()) 

    (loop StartPos src).ToArray()
    
// lazy lex the whole source code
let TokenSeq lexer src =
    let rec loop pos src' =
        match NextToken lexer pos src' with
        | EOF -> seq []
        | Ret(token, rest) -> seq{ yield token; yield! loop (Move token.End 1) rest }
        | LexError(msg, pos) -> raise (LexErr(msg, pos))

    loop StartPos src

let TokenList lexer src = 
    Tokens lexer src
    |> Array.toList

let private firstMatch lexer pos src =
    let rec loop pos src' =
        match NextToken lexer pos src' with
        | EOF -> ValueNone
        | Ret token -> ValueSome token
        | _ -> 
            let symbol = Seq.head src
            let pos = if char symbol = '\n' then NewLine pos else Next pos
            loop pos (Seq.tail src)

    loop pos src

// find first match of the patterns given by the lexer
let FirstMatch lexer src = firstMatch lexer StartPos src


// find all token matched in the sourcecode, ignoring anything not matching
let AllMatches lexer src =
    let mutable tokens = ResizeArray()
    let rec loop pos src =
        firstMatch lexer pos src
        |> ValueOption.iter (fun (token, rest) ->
            tokens.Add token
            loop (Next token.End) rest
        ) 

    loop StartPos src
    tokens

