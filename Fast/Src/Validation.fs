module Validation

open Ast
open Position
open Type
open Table
open Err

(*
    it is important to notice
    that the type validation do not care about the specifics of
    read/write to memeory despite consistency in types.

    the type intantiation part in the second fase will infere specific types depend 
    on use


*)

let TypeOfValue v =
    match v with
    | S8   _ -> u8  
    | S16  _ -> u16 
    | S32  _ -> u32 
    | S64  _ -> u64 
    | U8   _ -> s8  
    | U16  _ -> s16 
    | U32  _ -> s32 
    | U64  _ -> s64 
    | F32  _ -> f32 
    | F64  _ -> f64 
    | F128 _ -> f128


let inline AddType info t = { info with Ty = ValueSome t }

let TypeOfUnOp op =
    match op with
    | Neg           -> Num()
    | Sqrt          -> Floating()
    | Ceil          -> Floating()
    | Floor         -> Floating()
    | Round         -> Floating()
    | TrailingZeros -> Int()
    | LeadingZeros  -> Int()
    | IsZero        -> Int()
    | BitCount      -> Int()

let TypeOfBinOp op =
    match op with
    | ShiftLeft  -> Int()
    | ShiftRight -> Int()
    | RotLeft    -> Int()
    | RotRight   -> Int()
    | And        -> Int()
    | Or         -> Int()
    | Xor        -> Int()
    | Rem        -> Int()
    | Add        -> Num()
    | Sub        -> Num()
    | Div        -> Num()
    | Mul        -> Num()


let inline TypeOf info = (GetInfo info).Ty.Value

let mutable functioninstances = []

let AddInstance (name: string) (inst: Type) =
    // lookup instances by name
    List.tryFind (fun (n, _ : Type list) -> name = n) functioninstances
    |> Option.map snd // get instances
    // add instance
    |> Option.map (fun insts -> 
        functioninstances <- List.distinctBy fst ((name, (inst :: insts)) :: functioninstances))
    |> Option.defaultWith (fun _ -> functioninstances <- (name, [inst]) :: functioninstances)


    
let Swap ro =
    match ro with
    | ValueSome(Ok ro) ->Ok(ValueSome ro)
    | ValueSome(Error err) -> Error err
    | _ -> Ok ValueNone

let Bind = Result.bind

let Map = Result.map

let MapErr = Result.mapError

let GetOp op =
    match op with
    | S8   op -> S8   , op
    | S16  op -> S16  , op
    | S32  op -> S32  , op
    | S64  op -> S64  , op
    | U8   op -> U8   , op
    | U16  op -> U16  , op
    | U32  op -> U32  , op
    | U64  op -> U64  , op
    | F32  op -> F32  , op
    | F64  op -> F64  , op
    | F128 op -> F128 , op

let inline Bind2 f ret1 ret2 =
    match ret1, ret2 with
    | Error err1, Error err2 ->
        Err.Add err2 err1
        |> Error
    | Error err, _
    | _, Error err -> Error err
    | Ok ret1, Ok ret2 -> f ret1 ret2

let inline Map2 f ret1 ret2 =
    match ret1, ret2 with
    | Error err1, Error err2 ->
        Err.Add err2 err1
        |> Error
    | Error err, _
    | _, Error err -> Error err
    | Ok ret1, Ok ret2 -> Ok(f ret1 ret2)

let VMap f opr =
    match ValueOption.map (Map f) opr with
    | ValueSome(Ok ret) -> Ok(ValueSome ret) 
    | ValueSome(Error err) -> Error err
    | ValueNone -> Ok ValueNone

let rec ValidateExpr vtab ftab expr = 
    match expr with    
    | Value(v, info) -> 
        let t = TypeOfValue v
        Ok(Value(v, AddType info t))
    
    | Loc(l, info) -> 
        ValidateLocation vtab ftab l
        |> Map (fun l -> 
            let t = TypeOf l
            Loc(l, AddType info t)
        )

    | Unary(op, expr, info) ->
        let opt = TypeOfUnOp op
        ValidateExpr vtab ftab expr
        |> Bind (fun expr ->
            Unify opt (TypeOf expr)
            |> MapErr (fun err -> { err with Position = GetPos info})
            |> Map (fun t -> Unary(op, expr, AddType info t)))

    | Binary(op, left, right, info) ->
        let left = 
            ValidateExpr vtab ftab left
            |> MapErr (fun err -> { err with Position = GetPos info})
        let right =
            ValidateExpr vtab ftab right
            |> MapErr (fun err -> { err with Position = GetPos info})
        
        (left, right)
        ||> Bind2 (fun left right -> 
                Unify (TypeOf left) (TypeOf right)
                |> Bind (Unify (TypeOfBinOp op))
                |> Map (fun t -> 
                    Binary(op, left, right, AddType info t))
        )

    | Compare(op, left, right, info) ->
        let left = 
            ValidateExpr vtab ftab left
            |> MapErr (fun err -> { err with Position = GetPos info})
        let right =
            ValidateExpr vtab ftab right
            |> MapErr (fun err -> { err with Position = GetPos info})
        
        (left, right)
        ||> Bind2 (fun left right -> 
                Unify (TypeOf left) (TypeOf right)
                |> Map (fun t -> Compare(op, left, right, AddType info bool))
        )

    | Call(name, args, info) ->
        // validate arguments 
        let args = 
            Array.map (ValidateExpr vtab ftab) args 
            |> Array.fold (Map2 (fun args arg -> arg :: args)) (Ok[])
        
        args
        |> Bind (fun args -> 
            Lookup name ftab
            |> Bind (fun t -> 
                let args = List.toArray args |> Array.rev
                let f = Instantiate t
                let ret = Meta()
                let f' = func (Array.map TypeOf args) ret
                Unify f f'
                |> Map (fun _ -> 
                    AddInstance name (Generalize { values = [] } f')
                    Call(name, args, AddType info ret))
            )
        )

    | If(cond, meet, otherwise, info) ->
        let cond = ValidateExpr vtab ftab cond
        let meet = ValidateExpr vtab ftab meet 
        let otherwise = ValidateExpr vtab ftab otherwise

        Map TypeOf cond
        |> Bind (Unify bool) 
        |> Bind (fun _ ->
            (meet, otherwise)
            ||> Bind2 (fun meet otherwise -> 
                (TypeOf meet, TypeOf otherwise)
                ||> Unify
                |> Map2 (fun cond t -> If(cond, meet, otherwise, AddType info t)) cond
            )
        )

    | Convert(op, info) ->
        let op, expr = GetOp op
        let op', _ = GetOp (op())
        let expr = ValidateExpr vtab ftab expr
        let t = TypeOfValue (op())
        expr
        |> Map (fun expr -> Convert(op' expr, AddType info t))



and ValidateLocation (vtab: Table<string, Type * Mut>)  ftab loc =
    match loc with
    | Var (name, info) ->
        Lookup name vtab
        |> Map (fun (t, _) -> Var(name, AddType info t))
    
    | Adr(idx, info) ->
        ValidateExpr vtab ftab idx
        |> Bind (fun idx ->
            Unify adr (TypeOf idx)
            |> Map (fun _ -> Adr(idx, AddType info (Meta())))
        )


let inline AddLabel label labels =
    label
    |> ValueOption.map (fun label -> label :: labels)
    |> ValueOption.defaultValue labels

let rec ValidateStmt labels vtab ftab stmt =
    let inline Typeof (stmt, _,_) = TypeOf stmt
    match stmt with
    | Break (target, info) -> Ok(Break(target, AddType info unit), vtab, ftab)
    | Continue (target, info) -> Ok(Continue(target, AddType info unit), vtab, ftab)
    | Declare(name, mut, body, info) ->
        ValidateExpr vtab ftab body
        |> Map (fun body -> 
            let t = TypeOf body
            Declare(name, mut, body, AddType info t), Table.Bind name (t, mut) vtab, ftab
        )

    | Return(ret, info) ->
        ValidateExpr vtab ftab ret
        |> Map (fun ret -> Return(ret, AddType info (TypeOf ret)), vtab, ftab)

    | Assign(loc, value, info) ->
        let loc = ValidateLocation vtab ftab loc
        let value = ValidateExpr vtab ftab value

        (loc, value)
        ||> Bind2 (fun loc value ->
            // check type between the location and the value
            (TypeOf loc, TypeOf value)
            ||> Unify 
            |> Bind (fun _ -> 
                match loc with
                | Var(name, _) ->
                    Lookup name vtab
                    |> Bind (fun (_, mut) ->
                        if mut = Mut then
                            Ok(Assign(loc, value, AddType info unit), vtab, ftab)
                        else
                            // immutability are considered a type error
                            Err.Type $"the value {name} is immutable and cannot be updated" loc
                    )
                | _ ->
                    // address assignment are always mutable
                    Ok(Assign(loc, value, AddType info unit), vtab, ftab)
            )
        )

    | While(label, cond, body, info) ->
        let cond = ValidateExpr vtab ftab cond
        let body = ValidateStmt (AddLabel label labels) vtab ftab body
        (cond, body)
        ||> Bind2 (fun cond (body, _, _) -> 
            TypeOf cond
            |> Unify bool
            |> Map (fun _ -> 
                // it is legal to return in a while loop
                let t = TypeOf body
                While(label, cond, body, AddType info t), vtab, ftab
            )
        )

    // a call to the function can be allowed to return non unit
    // values without being nested inside a return statement
    // testing for unit type requirements are done in statement sequence validation
    | Execute(name, args, info) ->         
        Array.map (ValidateExpr vtab ftab) args 
        |> Array.fold (Map2 (fun args arg -> arg :: args)) (Ok[])
        |> Bind (fun args -> 
            Lookup name ftab
            |> Bind (fun t -> 
                let args = List.toArray args |> Array.rev
                let f = Instantiate t
                let ret = Meta()
                let f' = func (Array.map TypeOf args) ret
                Unify f f'
                |> Map (fun _ -> 
                    AddInstance name (Generalize { values = [] } f')
                    Execute(name, args, AddType info ret), vtab, ftab)
            )
        )

    | When(label, cond, meet, otherwise, info) ->
        let labels = AddLabel label labels
        let cond = ValidateExpr vtab ftab cond
        let meet = 
            ValidateStmt labels vtab ftab meet
            |> Map (fun (meet, _, _) -> meet)

        let otherwise = 
            ValueOption.map (ValidateStmt labels vtab ftab) otherwise
            |> Swap
            |> Map (fun otherwise ->
                match otherwise with
                | ValueNone -> ValueNone, vtab, ftab
                | ValueSome(otherwise, vtab, ftab) -> ValueSome otherwise, vtab, ftab
            )
            
        let o = 
            otherwise
            |> Map (fun (o, _, _) -> 
                ValueOption.map TypeOf o 
                |> ValueOption.defaultValue unit) 

        (Map TypeOf meet, o)
        ||> Bind2 Unify
        |> Bind (fun t -> 
            (meet, otherwise)
            ||> Bind2 (fun meet (otherwise, vtab, ftab) -> 
                cond
                |> Bind (fun cond ->
                    Unify bool (TypeOf cond)
                    |> Map (fun _ -> When(label, cond, meet, otherwise, AddType info t), vtab, ftab)
                )
            )    
        )

    // we can have sequences of statements which in branches end with a return statment.
    // this and the next case checks for that
    | Sequence(When(label, cond, meet, ValueNone, winfo), next, sinfo) ->
        let labels' = AddLabel label labels
        let cond = ValidateExpr vtab ftab cond
        let meet = ValidateStmt labels' vtab ftab meet       
        let next = ValidateStmt labels vtab ftab next

        (Map Typeof meet, Map Typeof next)
        ||> Bind2 Unify 
        |> Bind (fun t ->
            cond
            |> Bind (fun cond ->
                Unify bool (TypeOf cond) 
                |> Bind (fun _ ->
                   (next, meet)
                   ||> Map2 (fun (meet, _,_) (next,_,_) ->
                        Sequence(
                            // the type can possible be unit, this is just a generalized
                            // version for an if condition with a possible return statement
                            // and an empty else statement sequence
                            // followed by some statement sequence
                            // it checks that the branch are the same type
                            // as the following sequence
                            When(label, cond, meet, ValueNone, AddType winfo t), 
                            next, 
                            AddType sinfo t
                        ), vtab, ftab
                   )
                )
            )
        )

    // first is a none branching statement by invarians of parsing
    // hence, it must be of type unit, but the following statement sequence
    // can differ from unit, this allows for a sequence of unit typed statements
    // to be followed by a non unit typed statement.
    // this is needed becuase of sequences like
    //
    // when cond1 then
    //     ...
    //     return ..
    // when cond2 then
    //     ...
    //     return ..
    // ...
    // 
    // the case above covers the 'when' case
    | Sequence(first, next, info) ->
        let first = ValidateStmt labels vtab ftab first
        // need to take into account that first can have a declaration of a variable
        let next = 
            first
            |> Bind (fun (_, vtab, ftab) -> ValidateStmt labels vtab ftab next)

        Map Typeof first
        |> Map (Unify unit) 
        |> (fun t -> next, t) // need to check for type error
        ||> Bind2 (fun (next, _, _) _ -> 
            Map (fun (first, _, _) -> Sequence(first, next, AddType info (TypeOf next)), vtab, ftab) first
        )



and ValidataDeclarations vtab ftab dec = 
    match dec with 
    | Function(name, params, body, info) ->
        let paramType = Array.map (fun _ -> Meta()) params
        let ret = Meta()
        let ft = 
            (paramType, ret)
            ||> func

        let vtab' = BindAll params (Array.map (fun t -> (t, Imm)) paramType) vtab 
        let ftab' = Table.Bind name ft ftab
        ValidateStmt [] vtab' ftab' body
        |> Bind (fun (body, vtab, ftab) -> 
            Unify (TypeOf body) ret
            |> Map (fun _ ->
                let gft = Generalize vtab ft
                Function(name, params, body, AddType info gft), vtab, Table.Bind name gft ftab
            )
            )

    | Variable(name, mut, body, info) ->
        ValidateExpr vtab ftab body
        |> Map (fun body -> 
            let t = TypeOf body
            Variable(name, mut, body, AddType info t), Table.Bind name (t, mut) vtab, ftab
        )


and ValidateModule m = 
    (Ok([],{ values = []}, { values = []}), m.Declarations)
    ||> Array.fold (fun prior dec ->
        prior
        |> Bind (fun (decs, vtab, ftab) -> 
            ValidataDeclarations vtab ftab dec
            |> Map (fun (dec, vtab, ftab) -> dec :: decs, vtab, ftab)
        )
    )
    |> Map (fun (decs, _, _) -> 
        List.toArray decs
        |> Array.rev
        |> fun decs -> { m with Declarations = decs }
    )
    