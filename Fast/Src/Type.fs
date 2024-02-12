module Type

(*
    very basic polymorphic type system

    used to partial infere values
*)

open Err
open Ast
open Table
open Position

let empty = Table.Empty 

let Map2 f ret1 ret2 =
    match ret1, ret2 with
    | Error err, _
    | _, Error err -> Error err

    | Ok ret1, Ok ret2 -> Ok (f ret1 ret2) 
    
let Num() = Num(tyvar(), ref ValueNone)
let Int() = Int(tyvar(), ref ValueNone)
let Floating() = Floating(tyvar(), ref ValueNone)
let Meta() = Meta(tyvar(), ref ValueNone)



let rec Subst vtab t =
    match t with
    // the type group check happens on instantiaten
    | NVar name ->
        Lookup name vtab
        |> Result.map (Subst vtab)
        |> Result.bind (Unify (Num()))
        |> Result.defaultValue t 

    | IVar name ->
        Lookup name vtab
        |> Result.map (Subst vtab)
        |> Result.bind (Unify (Int()))
        |> Result.defaultValue t 
    
    | FVar name ->
        Lookup name vtab
        |> Result.map (Subst vtab)
        |> Result.bind (Unify (Floating()))
        |> Result.defaultValue t 
    
    | TyVar name ->
        Lookup name vtab
        |> Result.map (Subst vtab)
        |> Result.defaultValue t 

    | App(TyFun(tvs, t), tys) ->
        BindAll tvs tys empty
        |> subst t
        |> Subst vtab

    | App(tc, tys) -> App(tc, Array.map (Subst vtab) tys)
        
    | Poly(tvs, t) ->
        let gammas = Array.map (fun  _ -> tyvar()) tvs
        (tvs, Array.map TyVar gammas, empty)
        |||> BindAll
        |> subst t
        |> fun t -> Poly(gammas, t)

    | Num(_, it)
    | Int(_, it)
    | Floating(_, it)
    | Meta(_, it) ->
        it.Value
        |> ValueOption.map (Subst vtab)
        |> ValueOption.defaultValue t

    | _ -> t
 
and subst t vtab = Subst vtab t


and Expand t =
    match t with
    | App(TyFun(tvs, t), tys) ->
        BindAll tvs tys empty
        |> subst t
        |> Expand

    | App(Unique(tc, _), ts) ->
        App(tc, ts)
        |> Expand

    | Meta(_, it) ->
        it.Value
        |> ValueOption.map Expand
        |> ValueOption.defaultValue t

    | _ -> t

and Occurs m t =
    match t with
    | Meta(v, ti)
    | Floating(v, ti)
    | Int(v, ti)
    | Num(v, ti) -> 
        let ret = v = m
        ti.Value
        |> ValueOption.map (fun t -> ret || Occurs m t)
        |> ValueOption.defaultValue ret

    | Poly(_, t) -> Occurs m t
    | App(tc, ts) -> OccursInTc m tc || Array.exists (Occurs m) ts
    | _ -> false

and OccursInTc m tc =
    match tc with
    | Unique(tc, _) -> OccursInTc m tc
    | TyFun(_, t) -> Occurs m t
    | _ -> false


and Unify t1 t2 =
    match t1, t2 with
    | Int(a, _), Int(b, _) 
    | Num(a, _), Num(b, _) 
    | Floating(a, _), Floating(b, _) 
    | Meta(a, _), Meta(b, _) when a = b -> Ok t1
    | Meta(a, _), t
    | Num(a, _), t
    | t, Num(a, _)
    | Int(a, _), t
    | t, Int(a, _)
    | Floating(a, _), t
    | t, Floating(a, _)
    | t, Meta(a, _) when Occurs a t -> Err.Type $"Cyclic type" StartPos
    | (Meta _ as m), (App(TyFun _, _) as t)
    | (App(TyFun _, _) as t), (Meta _ as m) ->
        (m, Expand t)
        ||> Unify

    | t, Meta(_, ti) 
    | Meta(_,ti), t ->
        ti.Value
        |> ValueOption.map(fun t' ->
            Unify t t'
        )
        |> ValueOption.defaultWith (fun _ ->
            ti.Value <- ValueSome t
            Ok t
        )

    | Floating _, Int _
    | Int _, Floating _ -> Err.Type "integers and floats are not unifiable" StartPos


    | (Int _ as t), Num(_, ti)
    | Num(_, ti), (Int _ as t)
    | (Floating _ as t), Num(_, ti)
    | Num(_, ti), (Floating _ as t)
    | (App(Type _, _) as t), Num(_, ti)
    | Num(_, ti), (App(Type _, _) as t) ->
        ti.Value
        |> ValueOption.map (Unify t) 
        |> ValueOption.defaultWith (fun _ ->
            ti.Value <- ValueSome t
            Ok t
            )

    | Int(_, ti), t
    | t, Int(_, ti) when t |> Is integer ->
        ti.Value
        |> ValueOption.map (Unify t)
        |> ValueOption.defaultWith (fun _ ->
            ti.Value <- ValueSome t
            Ok t
        )

    | Floating(_, ti), t
    | t, Floating(_, ti) when t |> Is floating ->
        ti.Value
        |> ValueOption.map (Unify t)
        |> ValueOption.defaultWith (fun _ ->
            ti.Value <- ValueSome t
            Ok t
        )

    | IVar v1, IVar v2
    | NVar v1, NVar v2
    | FVar v1, FVar v2
    | TyVar v1, TyVar v2 when v1 = v2 -> Ok t1

    | App(TyFun(tvs, t), tys), t'
    | t', App(TyFun(tvs, t), tys) ->
        BindAll tvs tys empty
        |> subst t
        |> Unify t'

    | App(Unique(tc, z), ts), App(Unique(_, z'), ts') when z = z' ->
        UnifyAll ts ts'
        |> Result.map (fun ts -> App(Unique(tc, z), ts))

    | App(tc, ts), App(tc', ts') when tc = tc' ->
        UnifyAll ts ts'
        |> Result.map (fun ts -> App(tc, ts))

    | Poly(tvs, t), Poly(uvs, u) ->
        (uvs, Array.map TyVar tvs, empty)
        |||> BindAll
        |> subst u
        |> Unify t

    | Nil, (App(Struct _, _) as t)
    | (App(Struct _, _) as t), Nil -> Ok t

    | _ -> Err.Type $"the type {t1} and {t2} are not unifiable" StartPos



and UnifyAll ts1 ts2 =
    Array.map2 Unify ts1 ts2
    |> fun ts -> Array.foldBack (fun t ts -> Map2 (fun t ts -> t :: ts) t ts) ts (Ok [])
    |> Result.map (List.toArray >> Array.rev)



let Instantiate t =
    match t with
    | Poly(tvs, t) ->
        let tys = Array.map (fun _ -> Meta()) tvs
        (tvs, tys, empty)
        |||> BindAll
        |> subst t

    | _ -> t

let Generalize vtab t =
    let vs = 
        vtab.values
        |> List.map ItemOf 
        |> List.toArray


    let rec generalize t =
        match t with
        | Meta(v, ti)     
        | Num(v, ti)
        | Int(v, ti)
        | Floating(v, ti) when Array.exists (Occurs v) vs -> ([], Subst empty t)
        | Meta(v, ti) ->    
            ti.Value
            |> ValueOption.map generalize
            |> ValueOption.defaultWith (fun _ -> 
                let tv = tyvar()
                [tv], TyVar(tv)
                )

        | Num(v, ti) ->    
            ti.Value
            |> ValueOption.map generalize
            |> ValueOption.defaultWith (fun _ -> 
                let tv = tyvar()
                [tv], NVar(tv)
                )

        | Int(v, ti) ->    
            ti.Value
            |> ValueOption.map generalize
            |> ValueOption.defaultWith (fun _ -> 
                let tv = tyvar()
                [tv], IVar(tv)
                )

        | Floating(v, ti) ->    
            ti.Value
            |> ValueOption.map generalize
            |> ValueOption.defaultWith (fun _ -> 
                let tv = tyvar()
                [tv], FVar(tv)
                )

        | App(tc, ts) ->
            let ts', tc = generalizeTc tc
            let tss, ts =
                Array.map generalize ts
                |> Array.unzip
                
                
            List.concat (ts' :: List.ofArray tss), App(tc, ts)

        | Poly(_, t) -> generalize t

        | _ -> [], t

    and generalizeTc tc =
        match tc with
        | TyFun(tvs, t) -> 
            let ts, t = generalize t
            ts, TyFun(tvs, t)

        | Unique(tc, z) ->
            let ts, tc = generalizeTc tc
            ts, Unique(tc, z)

        | _ -> [], tc

    let ts, t = generalize t
    Poly(Array.ofList ts, t)


