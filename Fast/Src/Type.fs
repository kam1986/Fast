module Type

(*
    very basic polymorphic type system

    used to partial infere values
*)

open Ast
open Table

type TyCon =
    | Arrow
    | Type of Operator<unit,unit,unit>
    | TyFun of int[] * Type

and Type =
    | App  of TyCon * Type[]
    | Var  of int
    | FVar of int
    | SVar of int
    | UVar of int
    | Meta of int * Type voption ref
    | Signed of int * Type voption ref
    | Unsigned of int * Type voption ref
    | Floating of int * Type voption ref
    | Poly of int[] * Type

// this will lead to minimizing of memory usage
// since reference to the same value/memorypoint
let u8 = App(Type(U8()),    [||])
let u16 = App(Type(U16()),  [||])
let u32 = App(Type(U32()),  [||])
let u64 = App(Type(U64()),  [||])
let s8 = App(Type(S8()),    [||])
let s16 = App(Type(S16()),  [||])
let s32 = App(Type(S32()),  [||])
let s64 = App(Type(S64()),  [||])
let f32 = App(Type(F32()),  [||])
let f64 = App(Type(F64()),  [||])
let f128 = App(Type(F128()),[||])
let empty = Table.Empty 

let signed = 
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

let unsigned = 
    [|
        u8 
        u16
        u32
        u64
    |]

let floating = 
    [|
        f32
        f64
        f128
    |]

let rec Subst vc t tab =
    let inline subst tab t = Subst vc t tab
    match t with
    | Var t' -> 
        // this is at the leaf of the type tree hence, doing recursive replacesment
        // here are the optimal solution
        Lookup t' tab
        |> Result.map (subst tab) 
        |> Result.defaultValue t

    | App(TyFun(vs, t), ts) ->
        BindAll vs ts tab
        |> Subst vc t
         
    | App(tc, ts) ->  App(tc, Array.map (subst tab) ts)

    | Poly(vs, t) ->
        let gammas = [|for c in 0 .. vs.Length-1 -> vc + c |]
        let tab' = BindAll gammas (Array.map Var vs) tab
        Poly(gammas, Subst (vc + vs.Length) t tab')

    | Signed(_, ti)
    | Unsigned(_, ti)
    | Floating(_, ti)
    | Meta(_, ti) ->
        ti.Value
        |> ValueOption.map (subst tab) // recursive call to the leaf node
        |> ValueOption.defaultValue t  // unintialized

        
let rec Expand t =
    match t with
    | App(TyFun(vs,t), ts) ->
        let tab = BindAll vs ts empty
        Subst 0 t tab
        |> Expand
    
    | Signed(_, ti)
    | Unsigned(_, ti)
    | Floating(_, ti)
    | Meta(_, ti) ->
        ti.Value
        |> ValueOption.map Expand
        |> ValueOption.defaultValue t

    | _ -> t

// all meta variables has a unique number so no overlap between different kinds
let rec Occurs m t =
    match t with
    | Signed(m', _)
    | Unsigned(m', _)
    | Floating(m', _)
    | Meta(m', _) when m' = m -> true


    | Signed(_, ti)
    | Unsigned(_, ti)
    | Floating(_, ti)
    | Meta(_, ti) -> 
        ti.Value
        |> ValueOption.map (Occurs m)
        |> ValueOption.defaultValue false

    | App(TyFun(_, t), ts) -> Occurs m t || Array.exists (Occurs m) ts
    | App(_, ts) -> Array.exists (Occurs m) ts
    | Poly(_, t) -> Occurs m t
    | Var _ -> false


let rec Unify t1 t2 =
    match t1, t2 with
    | SVar v, SVar v'
    | UVar v, UVar v'
    | FVar v, FVar v'
    | Var v, Var v' when v = v' -> t1
    | (Meta _ as m), (App(TyFun _, _) as tf)
    | (App(TyFun _,_) as tf), (Meta _ as m) ->
        Expand tf
        |> Unify m

    
    | Signed(m, _) ,  Signed(m', _)
    | Unsigned(m, _), Unsigned(m', _)
    | Floating(m, _), Floating(m', _)
    | Meta(m, _), Meta(m', _) when m = m' -> t1
    
    | Signed(m, _), t
    | Unsigned(m, _), t
    | Floating(m, _), t
    | Meta(m, _), t when Occurs m t -> failwith "cyclic type"


    | (Meta(_, ti) as m), t
    | t, (Meta(_, ti) as m) -> 
        ti.Value
        |> ValueOption.map (Unify t)
        |> ValueOption.defaultWith (fun _ ->
            ti.Value <- ValueSome t
            m
        )

    | (Signed(_, ti) as s), t
    | t, (Signed(_, ti) as s) when Array.contains t signed ->
        ti.Value
        |> ValueOption.map (Unify t)
        |> ValueOption.defaultWith (fun _ ->
            ti.Value <- ValueSome t
            s
        )

    | (Unsigned(_, ti) as u), t
    | t, (Unsigned(_, ti) as u) when Array.contains t unsigned ->
        ti.Value
        |> ValueOption.map (Unify t)
        |> ValueOption.defaultWith (fun _ ->
            ti.Value <- ValueSome t
            u
        )


    | (Floating(_, ti) as f), t
    | t, (Floating(_, ti) as f) when Array.contains t floating ->
        ti.Value
        |> ValueOption.map (Unify t)
        |> ValueOption.defaultWith (fun _ ->
            ti.Value <- ValueSome t
            f
        )


    | t, App(TyFun(vs, u), ts)
    | App(TyFun(vs, u), ts), t ->
        (u, BindAll vs ts empty)
        ||> Subst 0
        |> Unify t

    | App(tc, ts), App(tc', ts') when tc = tc' -> App(tc, Array.map2 Unify ts ts')
    | Poly(vs, u), Poly(vs', t) ->
        let tab = BindAll vs' (Array.map Var vs) empty
        Subst 0 t tab
        |> Unify u

    | _ -> failwith $"type error: {t1} and {t2} are not unifiable"

