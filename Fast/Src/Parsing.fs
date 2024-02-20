(*
    TODO:
        need to rewrite for better error handling implementation
        we do not use dotnet exception handler, but use a costume error type
        and error loggers depending on the compiler and interpreters running mode.

        and give better error messages

        expand information captured i.e. instead of start infoition safe range over expressions, statements, and declarations

*)
module Parsing

open Err
open Token
open Lexing
open Position
open Ast

type Result<'ok,'err> with
    static member orElse e ret =
        match ret with
        | Error _ -> e
        | _ -> ret

    static member orElseWith e ret =
        match ret with
        | Error _ -> e()
        | _ -> ret

let (<!) (t1: #IPos) (t2: #IPos) = (t1.GetPos.Offset >>> 1) < (t2.GetPos.Offset >>> 1)
let (<=) (t1: #IPos) (t2: #IPos) = (t1.GetPos.Offset >>> 1) <= (t2.GetPos.Offset >>> 1)
let (==) (t1: #IPos) (t2: #IPos) = t1.GetPos.Offset = t2.GetPos.Offset

let OnSameLineAs (t1: #IPos) (t2: #IPos) = t1.GetPos.Line = t2.GetPos.Line



let Bool v info = Value(S32 v, info)
let True =  Bool 1 Info.Bool
let False = Bool 0 Info.Bool



let Info (token: Token<_>) = 
    {
        Ty = ValueNone
        Start = token.Start
        End = token.End
    }



let unop =
    [|
        BC
        MINUS
        LZ
        TZ
    |]

let binop =
    [|
        PLUS
        MINUS
        STAR
        SLASH
        REM
        AND
        OR
        XOR
        LS
        RS
        LR
        RR
    |]

let relop =
    [|
        NE
        EQ
        LE
        LT
        GE
        GT
    |]

let cvtop = 
    [|
        Tag.S8
        Tag.S16
        Tag.S32
        Tag.S64
        Tag.U8
        Tag.U16
        Tag.U32
        Tag.U64
        Tag.F32
        Tag.F64
        Tag.F128
    |]

let Logic = [|LAND; OR; IMPLY|]

let (++) a1 a2 = Array.append a1 a2


let tyop = 
    [|
        Tag.S8
        Tag.S16
        Tag.S32
        Tag.S64
        Tag.U8
        Tag.U16
        Tag.U32
        Tag.U64
        Tag.F32
        Tag.F64
        Tag.F128
    |]



let assleft = [||]
let assright = [||]


let ToUnary token expr info =
    match token.Type with
    | MINUS -> Ok(Unary(Neg, expr, info))
    | BC    -> Ok(Unary(BitCount, expr, info))
    | LZ    -> Ok(Unary(LeadingZeros, expr, info))
    | TZ    -> Ok(Unary(TrailingZeros, expr, info))
    | CEIL  -> Ok(Unary(Ceil, expr, info))
    | FLOOR -> Ok(Unary(Floor, expr, info))
    | ROUND -> Ok(Unary(Round, expr, info))
    | SQRT  -> Ok(Unary(Sqrt, expr, info))
    | t     -> Err.Syntax $"expected a unary operator, but found the token {t}" info
        


let ToBinOp token info =
    match token.Type with
    | PLUS   -> Ok Add
    | MINUS  -> Ok Sub
    | SLASH  -> Ok Div
    | STAR   -> Ok Mul
    | REM    -> Ok Rem
    | AND    -> Ok And
    | OR     -> Ok Or
    | XOR    -> Ok Xor
    | LS     -> Ok ShiftLeft
    | RS     -> Ok ShiftRight
    | LR     -> Ok RotLeft
    | RR     -> Ok RotRight
    | t -> Err.Syntax $"expected a binary operator, but found the token {t}" info

    
let ToRelOp token info =
    match token.Type with
    | NE -> Ok Ne 
    | EQ -> Ok Eq
    | LE -> Ok Le 
    | LT -> Ok Lt 
    | GE -> Ok Ge 
    | GT -> Ok Gt 
    | t -> Err.Syntax $"expected a relational operator, but found the token {t}" info


let ToCvtop token info =
   match token.Type with
   | Tag.S8   -> Ok Operator.S8   
   | Tag.S16  -> Ok Operator.S16  
   | Tag.S32  -> Ok Operator.S32  
   | Tag.S64  -> Ok Operator.S64  
   | Tag.U8   -> Ok Operator.U8   
   | Tag.U16  -> Ok Operator.U16  
   | Tag.U32  -> Ok Operator.U32  
   | Tag.U64  -> Ok Operator.U64  
   | Tag.F32  -> Ok Operator.F32  
   | Tag.F64  -> Ok Operator.F64  
   | Tag.F128 -> Ok Operator.F128 
   | t -> Err.Syntax $"expected a convertion operator, but found the token {t}" info


let inline Is set token = Array.contains token.Type set

let rec ParseValue tokens =
    match tokens with
    | { Type = TRUE } as token   :: tokens   -> Ok(Bool 1 (Info token), tokens)
    | { Type = FALSE } as token  :: tokens   -> Ok(Bool 0 (Info token), tokens)
    | { Type = SINT64 } as token :: tokens   -> Ok(Value (S64 (int64 token.Content), Info token), tokens)
    | { Type = SINT32 } as token :: tokens   -> Ok(Value (S32 (int token.Content), Info token), tokens)
    | { Type = SINT16 } as token :: tokens   -> Ok(Value (S16 (int16 token.Content), Info token), tokens)
    | { Type = SINT8 } as token  :: tokens   -> Ok(Value (S8 (int8 token.Content), Info token), tokens)
    | { Type = UINT64 } as token :: tokens   -> Ok(Value (U64 (uint64 token.Content), Info token), tokens)
    | { Type = UINT32 } as token :: tokens   -> Ok(Value (U32 (uint token.Content), Info token), tokens)
    | { Type = UINT16 } as token :: tokens   -> Ok(Value (U16 (uint16 token.Content), Info token), tokens)
    | { Type = UINT8 } as token  :: tokens   -> Ok(Value (U8  (uint8 token.Content), Info token), tokens)
   
    | { Type = FLOAT32 } as token :: tokens   -> Ok(Value (F32 (float32 token.Content), Info token), tokens)
    | { Type = FLOAT64 } as token :: tokens   -> Ok(Value (F64 (float token.Content), Info token), tokens)
    | { Type = FLOAT128 } as token :: tokens  -> Ok(Value (F128 (decimal token.Content), Info token), tokens)
    
    | ({ Type = ID } as token) :: ({ Type = LPARANT }) :: tokens  ->
        ParseArgs token tokens        
        |> Result.map (fun (args, tokens) -> Call(token.Content, args, Info token), tokens)
        
    |  { Type = ID } as token :: tokens  -> Ok(Loc(Var(token.Content, Info token), Info token), tokens)

    | { Type = LPARANT } as lp :: tokens ->
        ParseLogic tokens
        |> Result.bind (fun (expr, tokens) -> 
            if lp <= expr then
                match tokens with
                | ({ Type = RPARANT } as rp) :: tokens when lp <= rp -> Ok(expr, tokens)
                | ({ Type = RPARANT } as rp) :: _ -> Err.Indentation $"closing ')' was not indented properly" (Info rp)
                | _ -> Err.Syntax $"expected a ')', but found the token" (Info lp)
            else Err.Indentation $"the nested expression was not properly indented in respect to the opening '('" (GetInfo expr)
        )
    | t :: _ -> Err.Syntax $"expected a value or a nested expression, but found {t}" (GetPos t)
    | _ -> Err.Syntax $"expected a value or a nested expression, but reach end of input" StartPos 


and ParseLoc tokens =
    match tokens with
    | { Type = ID } as token :: tokens -> Ok(Loc(Var(token.Content, Info token), Info token), tokens)
    | { Type = DEREF } as token :: tokens ->
        tokens
        |> ParseValue
        |> Result.map (fun (adr, tokens) -> Loc(Adr(adr,  GetInfo adr), Info token), tokens)

    | _ -> ParseValue tokens 
        

and ParseExpr tokens =
    match tokens with
    | token :: tokens when token |> Is unop ->
        ParseExpr tokens
        |> Result.bind (fun (expr, tokens) ->
            ToUnary token expr (Info token)
            |> Result.map (fun expr -> expr, tokens)
        )


    | { Type = IF } as i :: tokens ->
        ParseLogic tokens
        |> Result.bind (fun (cond, tokens) ->
            match tokens with
            | { Type = THEN } as t :: tokens when i <= t && i <! cond ->
                ParseExpr tokens
                |> Result.bind (fun (meet, tokens) ->
                    match tokens with
                    | { Type = ELSE } as e :: tokens when i <= e && i <! meet ->
                        ParseExpr tokens
                        |> Result.bind (fun (otherwize, tokens) ->
                            if i <! otherwize then 
                                Ok(If(cond, meet, otherwize, Info i), tokens)
                            else 
                                Err.Indentation "" otherwize
                        )
                    | { Type = ELSE } as e :: _ -> Err.Indentation "" e 
                    | t :: _ -> Err.Syntax "" t 
                    | _ -> Err.EOC meet
                )
            | { Type = THEN } as t :: _ -> Err.Indentation "" t 
            | _ -> Err.EOC i
            )

    | token :: tokens when token |> Is cvtop ->        
        ParseValue tokens
        |> Result.bind (fun (value, tokens) -> 
            if token <= value then
                ToCvtop token (GetPos token)
                |> Result.map(fun op -> Convert(op value, Info token), tokens)
            else
                Err.Indentation 
                    $"the argument to the convertion operator are not indented correctly" 
                    (GetPos token)
        )

    | _ -> 
        ParseValue tokens
        |> Result.bind (fun (left, tokens) ->
            match tokens with
            // binary operations preceds relation operations
            | op :: tokens when op |> Is binop && left <= op ->
                ToBinOp op op
                |> Result.bind (fun op' ->
                    ParseExpr tokens
                    |> Result.map (fun (right, tokens) ->
                        match right with
                        | Binary (op'', left', right', info) when op'' < op' && left <= right ->
                            Binary(op', Binary(op', left, left', Info op), right', info), tokens
                        | _ -> Binary(op', left, right, Info op), tokens
                    )
                )
        
            | op :: tokens when op |> Is relop && left <= op -> // obs: since they return a integer sequences of relops are fine
                ToRelOp op op
                |> Result.bind (fun op' ->
                    ParseExpr tokens
                    |> Result.map (fun (right, tokens) ->  Compare(op', left, right, Info op), tokens)
                    )
            
            | _ -> Ok(left, tokens)
            )


and ParseArgs lp tokens =
    let rec loop args tokens =
        match tokens with
        | { Type = RPARANT } as rp :: tokens when lp <= rp -> 
            List.toArray args 
            |> Array.rev
            |> fun args -> Ok(args, tokens)

        | t :: tokens when lp <= t ->
            ParseExpr tokens
            |> Result.bind (fun (arg, tokens) ->
                match tokens with
                | { Type = COMMA } as c :: tokens when lp <= c -> loop (arg :: args) tokens
                | { Type = RPARANT} as rp :: tokens when lp <= rp -> 
                    List.toArray (arg :: args) 
                    |> Array.rev
                    |> fun args -> Ok(args, tokens)
                | { Type = COMMA } as c :: _ -> Err.Indentation "" c
                | { Type = RPARANT} as rp :: _ -> Err.Indentation "" rp
                | t :: _ -> Err.Syntax "" t 
            )
        
        | { Type = RPARANT } as rp :: _ ->
            Err.Indentation "the closing ')' are not indented properly" rp

        | t :: _ -> Err.Syntax $"expected a closing a closing ')', but found {t}" t

        | _ -> Err.EOC lp

    loop [] tokens

// we include logical implies "->" even though it 
// is nearly never used it is a easy implementation feature
// and it leads to an build in optimal pattern.
and ParseLogic tokens =
    match tokens with
    | { Type = NOT } as token :: tokens ->
        ParseExpr tokens
        |> Result.map (fun (e, tokens) -> Unary(IsZero, e, Info token), tokens)

    | _ ->
        ParseExpr tokens
        |> Result.bind (fun (left, tokens) ->
            match tokens with
            | { Type = LAND } as logop :: tokens ->
                ParseExpr tokens
                |> Result.map (fun (right, tokens) -> If(left, right, False, Info logop), tokens)
            
            | { Type = LOR } as logop :: tokens ->
                ParseExpr tokens
                |> Result.map (fun (right, tokens) -> If(left, True, right, Info logop), tokens)

            | { Type = IMPLY } as logop :: tokens ->
                ParseExpr tokens
                |> Result.map (fun (right, tokens) -> If(left, right, True, Info logop), tokens)

            | _ -> Ok(left, tokens)
        )
   

and ParseStmt tokens =
    match tokens with
    | { Type = CONTINUE } as t :: ({ Type = ID } as label) :: tokens when t <! label ->
        Ok(Continue(ValueSome label.Content, Info t), tokens)
    | { Type = BREAK } as t :: ({ Type = ID } as label) :: tokens when t <! label ->
        Ok(Break(ValueSome label.Content, Info t), tokens)
    
    | { Type = CONTINUE } as t :: tokens -> Ok(Continue(ValueNone, Info t), tokens)
    | { Type = BREAK } as t :: tokens -> Ok(Break(ValueNone, Info t), tokens)
    | { Type = MUT } as mut :: ({ Type = ID } as id) :: { Type = EQ } :: tokens ->
        ParseLogic tokens
        |> Result.map (fun (body, tokens) -> Declare(id.Content, Mut, body, Info mut), tokens)

    | { Type = LET } as mut :: ({ Type = ID } as id) :: { Type = EQ } :: tokens ->
        ParseLogic tokens
        |> Result.map (fun (body, tokens) -> Declare(id.Content, Imm, body, Info mut), tokens)

    | { Type = RETURN } as ret :: tokens ->
        ParseLogic tokens        
        |> Result.map (fun (e, tokens) -> Return(e, Info ret), tokens)

    | { Type = WHEN } as w :: ({ Type = ID } as id) :: tokens when w <! id ->
        ParseLogic tokens
        |> Result.bind (fun (cond, tokens) -> 
            match tokens with
            | { Type = DO } as d :: tokens when d == w || d |> OnSameLineAs w ->
                ParseStmtSeq w tokens
                |> Result.bind (fun (meet, tokens) -> 
                    match tokens with
                    | { Type = ELSE } as e :: tokens when e == w || e |> OnSameLineAs w ->
                        ParseStmtSeq w tokens
                        |> Result.orElse (Ok(When(ValueNone, cond, meet, ValueNone, Info w), tokens))
                        |> Result.map (fun (otherwise, tokens) -> When(ValueSome id.Content, cond, meet, ValueSome otherwise, Info w), tokens
                        )
                    | _ -> Ok(When(ValueSome id.Content, cond, meet, ValueNone, Info w), tokens)
                )
            | _ -> Err.Syntax "" cond
            )

    | { Type = WHEN } as w :: tokens ->
        ParseLogic tokens
        |> Result.bind (fun (cond, tokens) -> 
            match tokens with
            | { Type = DO } as d :: tokens when d == w || d |> OnSameLineAs w ->
                ParseStmtSeq w tokens
                |> Result.bind (fun (meet, tokens) -> 
                    match tokens with
                    | { Type = ELSE } as e :: tokens when e == w || e |> OnSameLineAs w ->
                        ParseStmtSeq w tokens
                        |> Result.orElse (Ok(When(ValueNone, cond, meet, ValueNone, Info w), tokens))
                        |> Result.map (fun (otherwise, tokens) -> When(ValueNone, cond, meet, ValueSome otherwise, Info w), tokens)
                    | _ -> Ok(When(ValueNone, cond, meet, ValueNone, Info w), tokens)
                )
            | _ -> Err.Syntax "" cond
        )

    | { Type = ID } as exe :: ({ Type = LPARANT } as lp) :: tokens ->
        ParseArgs lp tokens
        |> Result.map (fun (args, tokens) -> Execute(exe.Content, args, Info exe), tokens)

    | { Type = WHILE } as w :: ({ Type = ID} as id) :: tokens ->
        ParseLogic tokens
        |> Result.bind (fun (cond, tokens) -> 
            if w <! cond then
                match tokens with
                | { Type = DO } as d :: tokens when w == d || d |> OnSameLineAs w ->
                    ParseStmtSeq w tokens
                    |> Result.map (fun (body, tokens) -> While(ValueSome id.Content, cond, body, Info w), tokens)
                | _ -> Err.Syntax "" cond
            else
                Err.Indentation "" cond
        )

    | { Type = WHILE } as w :: tokens ->
        ParseLogic tokens
        |> Result.bind (fun (cond, tokens) ->
        if w <! cond then
            match tokens with
            | { Type = DO } as d :: tokens when w == d || d |> OnSameLineAs w ->
                ParseStmtSeq w tokens
                |> Result.map (fun (body, tokens) -> While(ValueNone, cond, body, Info w), tokens)
            | t :: _ -> Err.Syntax $"expecte a do bout found token {t}" w
            | _ -> Err.EOC cond
        else
            Err.Indentation "the condition of the while loop are not indented properly" w
        )

    | _ ->
        ParseLoc tokens
        |> Result.bind (fun (Loc(loc, _), tokens) ->
            match tokens with
            | { Type = ARROW } as a :: tokens ->
                ParseExpr tokens
                |> Result.map (fun (value, tokens) -> Assign(loc, value, GetInfo loc), tokens)
            | t :: _ -> Err.Syntax $"expected an assignment operator '<-' but found {t}" loc
            | _ -> Err.EOC loc
        )


and ParseStmtSeq token tokens =
    let rec loop stmt tokens =
        match tokens with        
        // indentation check of body
        | t :: _ when token <! t && token.Start.Line < (GetPos t).Line  -> 
            ParseStmt tokens
            |> Result.bind (fun (stmt', tokens) -> 
                let stmt = 
                    ValueOption.map (fun stmt -> Sequence(stmt, stmt', GetInfo stmt)) stmt
                    |> ValueOption.orElse (ValueSome stmt')
                    
                loop stmt tokens                )
    
        | _ -> Ok(stmt, tokens)

    loop ValueNone tokens
    |> Result.bind (fun (stmtopt, tokens) ->
        stmtopt
        |> ValueOption.map (fun stmt -> Ok(stmt, tokens))
        |> ValueOption.defaultValue (Err.Syntax "statement sequence was not found" token)
    )
    

// we could simple insert type variables instead of a valueoption type 
// but we choose to address this later
and ParseParams tokens =
    let rec loop params tokens =
        match tokens with
        | { Type = RPARANT } :: tokens -> 
            List.toArray params |> Array.rev, tokens

        | { Type = ID } as param :: ty :: { Type = RPARANT } :: tokens 
            when ty |> Is tyop ->
            let tyop =
                ToCvtop ty ty
                |> Result.map (fun t -> App(Type (t()), [||]))
                |> Result.defaultWith (fun _ -> failwith "should never happen param typing 1")

            List.toArray (param.Content :: params) |> Array.rev, tokens

        | { Type = ID } as param :: { Type = RPARANT} :: tokens ->
            List.toArray (param.Content :: params) |> Array.rev, tokens
    
        | { Type = ID } as param :: { Type = COMMA } :: tokens ->
            loop (param.Content :: params) tokens

    loop [] tokens
    |> Ok



and ParseDec at tokens =
    match tokens with
    | { Type = LET } as v :: ({ Type = ID } as id) :: { Type = EQ } :: tokens ->
        ParseLogic tokens
        |> Result.map (fun (body, tokens) -> Variable(id.Content, Imm, body, Info v), tokens)

    | { Type = MUT } as v :: ({ Type = ID } as id) :: { Type = EQ } :: tokens ->
        ParseLogic tokens
        |> Result.map (fun (body, tokens) -> Variable(id.Content, Mut, body, Info v), tokens)

    | { Type = FUN } as f :: ({ Type = ID } as id) :: { Type = LPARANT } :: tokens ->
        ParseParams tokens
        |> Result.bind (fun (params, tokens) ->
            ParseStmtSeq f tokens
            |> Result.map (fun (body, tokens) -> Function(id.Content, params, body, Info f), tokens)            
        )
    | t :: _ -> Err.Syntax $"expecting a declaration token but found {t}" t 
    | _ -> Err.EOC at



and ParseModule tokens =
    let rec loop at decs tokens =
        match tokens with
        | [] -> 
            List.toArray decs 
            |> Array.rev
            |> Ok
        | _ -> 
            ParseDec at tokens
            |> Result.bind (fun (dec, tokens) -> loop at (dec :: decs) tokens)

    match tokens with
    | { Type = MODULE } :: ({ Type = ID } as id) :: tokens ->
        loop id.End [] tokens
        |> Result.map (fun decs -> 
            {   
                Name = id.Content
                Declarations = decs
                Exe = ValueNone
            }
        )

    | _ -> 
        loop StartPos [] tokens
        |> Result.map (fun decs ->
            {   
                Name = ""
                Declarations = decs
                Exe = ValueNone
            }
        )

