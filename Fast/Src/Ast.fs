module Ast


open Position
// used in different setting
[<Struct>]
type Operand<'s8, 's16, 's32, 's64, 'u8, 'u16, 'u32, 'u64,'f32, 'f64, 'f128> =
    | S8    of s8  : 's8
    | S16   of s16 : 's16
    | S32   of s32 : 's32
    | S64   of S64 : 's64
    | U8    of U8  : 'u8
    | U16   of u16 : 'u16
    | U32   of u32 : 'u32
    | U64   of u64 : 'u64
    | F32   of f32 : 'f32
    | F64   of f64 : 'f64
    | F128  of f128: 'f128



type Operator<'s,'u,'f> = Operand<'s, 's, 's, 's, 'u, 'u, 'u, 'u,'f, 'f, 'f>

// for now this is the only thing we need
// we will expand it to polymorphic types and use total type inference later on

type Value = Operand<int8, int16, int32, int64, uint8, uint16, uint32, uint64, float32, float, decimal>
   



and UnOp =
    | Neg
    | Sqrt
    | Ceil
    | Floor
    | Round
    | TrailingZeros
    | LeadingZeros
    | IsZero
    | BitCount
    


and BinOp =
    | ShiftLeft
    | ShiftRight
    | RotLeft
    | RotRight
    | And
    | Or
    | Xor
    | Add
    | Sub
    | Rem
    | Div
    | Mul


type RelOp =
    | Ne
    | Eq
    | Le
    | Lt
    | Ge
    | Gt


type Mut = 
    | Mut
    | Imm


and Expr =
    | Value of Value * Pos
    | Loc of Loc * Pos
    | Unary of UnOp * Expr * Pos
    | Convert of Operator<Expr, Expr, Expr> * Pos
    | Binary of BinOp * Expr * Expr * Pos
    | Compare of RelOp * Expr * Expr * Pos
    | Call of string * Expr[] * Pos // call function
    | If of Expr * Expr * Expr * Pos
with
    interface IPos with
        member E.GetPos =
            match E with
            | Value(_, pos) -> pos
            | Loc(_,pos)
            | Unary(_,_,pos)
            | Binary(_,_,_,pos)
            | Convert(_, pos)
            | Compare(_,_,_,pos)
            | Call(_,_,pos)
            | If(_,_,_,pos) -> pos


and Loc =
    | Var of string * Pos
    | Adr of Expr * Pos
with
    interface IPos with
        member L.GetPos = 
            match L with
            | Var(_, pos)
            | Adr(_, pos) -> pos

and Stmt =
    | Declare of string * Mut * Expr * Pos
    | Assign of Loc * Expr * Pos
    | When of string voption * Expr * Stmt[] * Stmt[] * Pos
    | Break of string voption * Pos    // optional targets, no target are implicit the inner most loop
    | Continue of string voption * Pos // optional targets, no target are implicit the inner most loop
    | While of string voption * Expr * Stmt[] * Pos
    | Execute of string * Expr[] * Pos // execute procedure
    | Return of Expr * Pos
with
    interface IPos with
        member S.GetPos =
            match S with
            | Declare(_,_,_,pos) 
            | Assign(_,_,pos)
            | When(_,_,_,_,pos)
            | Break(_,pos)
            | Continue(_, pos)
            | While(_,_,_,pos)
            | Execute(_,_,pos)
            | Return(_,pos) -> pos


type Declaration =
    | Function of string * string[] * Stmt[] * Pos
    | Variable of string * Mut * Expr * Pos
with
    interface IPos with
        member D.GetPos =
            match D with
            | Function(_,_,_,pos)
            | Variable(_,_,_,pos) -> pos


type Module =
    {
        Name: string
        Declarations: Declaration[]
        Exe: string voption
    }