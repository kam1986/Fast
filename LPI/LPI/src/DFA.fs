module DFA

open Regex


let private (</>) s1 s2 = Set.intersect s1 s2

[<Struct>]
type HasTransition  =
    val mutable tab: sbyte[]
    new size = { tab = Array.zeroCreate size }
    member HT.Item 
        with get(state, symbol) = HT.tab[255*state+symbol]
        and set(state, symbol) value = HT.tab[255*state+symbol] <- sbyte value


type DFATable =
     val table: int[]
     val hastransition: HasTransition
     val terminals: int[]
     internal new(tab,ht, t) = { table = tab; hastransition = ht; terminals = t }

     /// given a state and a symbol return either the next state number or -1
     /// since the table indexing only takes bytes it can only do lookup in the range of (0,255*256-1)
     /// hence there are no way of get out of bound
     member DFA.Item 
        with get(state, symbol) =
            let next = int DFA.table[int state * 256 + int symbol]
            // will return -1 if no legal transition, faster than branching
            next - (1 - int DFA.hastransition[state, symbol]) * (next + 1)
    

// si optimized
// TODO need to handle multiple 
let Construct (regex, count) =
    let followpos = Follow count regex
    let symbols = Symbols regex
    let posOfSymbols = PosOfSymbols regex
    let start = First regex
    
    let mutable marked = []
    let mutable unmarked = [start]
    let mutable Dtran = Map.empty
    while unmarked <> [] do
        let mutable unmarked' = []
        for S in unmarked do
            if not(List.contains S marked || Set.isEmpty S) then
                marked <- List.distinct (S :: marked)

            for a in symbols do
                let U = 
                    S </> posOfSymbols[a]
                    |> Set.fold (fun u p -> u + followpos[p]) (set [])
                
                if not(Set.isEmpty U) then
                    if not(List.contains U marked) then
                        unmarked' <- List.distinct (U :: unmarked')
                                        
                    Dtran <- Map.add struct(S,a) U Dtran
        unmarked <- unmarked'

    // set the starting start at location 0
    let Dstates = 
        start :: List.filter ((<>) start) marked
        |> List.toArray
        
    let Terminals = 
        Array.map (fun state -> Set.filter (fun i -> i < 0) state) Dstates
        |> Array.map (fun state -> 
            if Set.isEmpty state then 
                -1
            else 
                -state.MaximumElement-1
        )
    // rename states from set of positions to integers i.e indexes of states
    let Dtran' = 
        (Map.empty, Dtran)
        ||> Map.fold (fun dtran struct(state, symbol) item -> 
            Map.add struct(Array.findIndex ((=) state) Dstates, symbol) (Array.findIndex ((=) item) Dstates) dtran)
    

    // not the fastes way to do it, but more readable
    let mutable table = 
        [| for i in 0 .. Dstates.Length-1 -> 
            [| for s in 0uy .. 255uy ->
                (Map.tryFind struct(i, s) Dtran' |> Option.defaultValue 0)
            |]
        |]
        |> Array.concat

    let mutable ht = HasTransition(Dstates.Length*256)
    for state in 0 .. Dstates.Length-1 do
        for symbol in symbols do
            ht[state, int symbol] <- if Map.containsKey struct(state, symbol) Dtran' then 1 else 0

    DFATable(table, ht, Terminals)

