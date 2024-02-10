module Type

(*
    very basic polymorphic type system

    used to partial infere values
*)

open Ast
open Table
open Err

let empty = Table.Empty 

let Map2 f ret1 ret2 =
    match ret1, ret2 with
    | Error err1, Error err2 ->
        Err.Add err2 err1
        |> Error

    | Error err, _
    | _, Error err -> Error err

    | Ok ret1, Ok ret2 -> Ok (f ret1 ret2) 


let rec Subst c vtab t =
    match t with
    | IVar name
    | FVar name
    | NVar name
    | TyVar name ->
        Lookup name vtab
        |> Result.map (Subst c vtab)
        |> Result.defaultValue t 

    | App(TyFun(tvs, t), tys) ->
        BindAll tvs tys empty
        |> subst c t
        |> Subst c vtab

    | App(tc, tys) -> App(tc, Array.map (Subst c vtab) tys)
        
    | Poly(tvs, t) ->
        let gammas = Array.mapi (fun i _ -> i + c) tvs
        (tvs, Array.map TyVar gammas, empty)
        |||> BindAll
        |> subst (c + tvs.Length) t
        |> fun t -> Poly(gammas, t)

    | _ -> failwith ""
 
and subst c t vtab = Subst c vtab t


and Expand t =
    match t with
    | App(TyFun(tvs, t), tys) ->
        BindAll tvs tys empty
        |> subst 0 t
        |> Expand

    | _ -> t


and Unify t1 t2 =
    match t1, t2 with
    | IVar v1, IVar v2
    | NVar v1, NVar v2
    | FVar v1, FVar v2
    | TyVar v1, TyVar v2 when v1 = v2 -> Ok t1

    | App(TyFun(tvs, t), tys), t'
    | t', App(TyFun(tvs, t), tys) ->
        BindAll tvs tys empty
        |> subst 0 t
        |> Unify t'

    | App(tc, ts), App(tc', ts') when tc = tc' ->
        UnifyAll ts ts'
        |> Result.map (fun ts -> App(tc, ts))





and UnifyAll ts1 ts2 =
    Array.map2 Unify ts1 ts2
    |> fun ts -> Array.foldBack (fun t ts -> Map2 (fun t ts -> t :: ts) t ts) ts (Ok [])
    |> Result.map (List.toArray >> Array.rev)