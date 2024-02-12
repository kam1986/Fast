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

let mutable count = 0
    
let tyvar() =
    let t = count
    count <- count + 1
    t

// classes in F# has reference based equality
// hence two instances are always considered 
// unequal
type Unique() =
    class
    end


type TyCon =
    | Array 
    | Arrow
    | Str
    | Unit
    | Struct of string[]
    | Unique of TyCon * Unique
    | Type of Operator<unit,unit,unit>
    | TyFun of int[] * Type

and Type =
    | Nil
    | TyVar  of int
    | FVar of int
    | IVar of int
    | NVar of int
    | Meta of int * Type voption ref
    | Int of int * Type voption ref
    | Num of int * Type voption ref
    | Floating of int * Type voption ref
    | Poly of int[] * Type
    | App  of TyCon * Type[]

// this will lead to minimizing of memory usage
// since reference to the same value/memorypoint
let u8   = App(Type(U8()),  [||])
let u16  = App(Type(U16()), [||])
let u32  = App(Type(U32()), [||])
let u64  = App(Type(U64()), [||])
let s8   = App(Type(S8()),  [||])
let s16  = App(Type(S16()), [||])
let s32  = App(Type(S32()), [||])
let s64  = App(Type(S64()), [||])
let f32  = App(Type(F32()), [||])
let f64  = App(Type(F64()), [||])
let f128 = App(Type(F128()),[||])
let unit = App(Unit, [||])
let bool = s32
let adr  = u64

let func input ret = Array.foldBack (fun input ret -> App(Arrow, [|input; ret|])) input ret

let integer = 
    [|
        u8 
        u16
        u32
        u64
        s8 
        s16
        s32
        s64
    |]

let floating = 
    [|
        f32
        f64
        f128
    |]

let Is set s = Array.contains s set

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


type Info =
    {
        Start: Pos
        End: Pos
        Ty: Type voption
    }
with
    interface IPos with
        member I.GetPos = I.Start

    interface IInfo with
        member I.GetInfo = I

    static member Default = 
        {
            Start = StartPos
            End = StartPos
            Ty = ValueNone
        }

    static member Bool =
        {
            Start = StartPos
            End = StartPos
            Ty = ValueSome bool
        }

and [<Interface>] IInfo =
    abstract member GetInfo : Info


and Expr =
    | Value of Value * Info
    | Loc of Loc * Info
    | Unary of UnOp * Expr * Info
    | Convert of Operator<Expr, Expr, Expr> * Info
    | Binary of BinOp * Expr * Expr * Info
    | Compare of RelOp * Expr * Expr * Info
    | Call of string * Expr[] * Info // call function
    | If of Expr * Expr * Expr * Info
with
    interface IPos with
        member E.GetPos =
            match E with
            | Value(_, pos) -> GetPos pos
            | Loc(_,pos)
            | Unary(_,_,pos)
            | Binary(_,_,_,pos)
            | Convert(_, pos)
            | Compare(_,_,_,pos)
            | Call(_,_,pos)
            | If(_,_,_,pos) -> GetPos pos

    interface IInfo with
        member I.GetInfo =
            match I with
            | Value(_, pos) -> pos
            | Loc(_,pos)
            | Unary(_,_,pos)
            | Binary(_,_,_,pos)
            | Convert(_, pos)
            | Compare(_,_,_,pos)
            | Call(_,_,pos)
            | If(_,_,_,pos) -> pos 

and Loc =
    | Var of string * Info
    | Adr of Expr * Info
with
    interface IPos with
        member L.GetPos = 
            match L with
            | Var(_, pos)
            | Adr(_, pos) -> GetPos pos

    interface IInfo with
        member L.GetInfo = 
            match L with
            | Var(_, pos)
            | Adr(_, pos) -> pos

and Stmt =
    | Declare of string * Mut * Expr * Info
    | Assign of Loc * Expr * Info
    | When of string voption * Expr * Stmt * Stmt voption * Info
    | Break of string voption * Info    // optional targets, no target are implicit the inner most loop
    | Continue of string voption * Info // optional targets, no target are implicit the inner most loop
    | While of string voption * Expr * Stmt voption * Info
    | Execute of string * Expr[] * Info // execute procedure
    | Return of Expr * Info
    // used instead of an array since it makes type validation easier.
    | Sequence of Stmt * Stmt * Info 
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
            | Sequence(_,_,pos)
            | Return(_,pos) -> GetPos pos

    interface IInfo with
        member S.GetInfo =
            match S with
                | Declare(_,_,_,pos) 
                | Assign(_,_,pos)
                | When(_,_,_,_,pos)
                | Break(_,pos)
                | Continue(_, pos)
                | While(_,_,_,pos)
                | Execute(_,_,pos)
                | Sequence(_,_,pos)
                | Return(_,pos) -> pos


let GetInfo (a: #IInfo) = a.GetInfo

type Declaration =
    | Function of string * string[] * Stmt voption * Info
    | Variable of string * Mut * Expr * Info
with
    interface IPos with
        member D.GetPos =
            match D with
            | Function(_,_,_,pos)
            | Variable(_,_,_,pos) -> GetPos pos


type Module =
    {
        Name: string
        Declarations: Declaration[]
        Exe: string voption
    }