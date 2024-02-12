module Table

open Err
open Position


let inline KeyOf (struct(key, _)) = key
let inline ItemOf (struct(_, item)) = item

// the use of 'struct' are to inline that pair in the list node as a tuple
// instead as a pointer to a tuple this will decrease memory comsumption
// and increase lookup speed because there are less sparse memory access approximate 1/2
[<Struct>]
type Table<'key,'item when 'key: equality> = { values: struct('key * 'item) list }
with static member Empty = { values = [] } : Table<'key,'item>

let Bind key item tab = { values = struct(key, item) :: tab.values }

let BindAll keys items tab =
    { values =
        (tab.values, keys, items)
        |||> Seq.fold2 (fun pairs key item -> struct(key, item) :: pairs)
    }

let Lookup key tab =
    let rec loop values =
        match values with
        | [] -> Err.LookUp $"the identifier {key} was not found" StartPos
        | pair :: _ when KeyOf pair = key -> 
            pair 
            |> ItemOf 
            |> Ok
        | _ :: rest -> loop rest
    loop tab.values


let Union tab1 tab2 = { values = List.distinct (tab1.values @ tab2.values) }
