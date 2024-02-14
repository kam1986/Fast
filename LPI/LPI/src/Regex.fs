module Regex
#nowarn "86"
// minimal set of a regex tree type
type Regex =
    | Epsilon
    | Terminal of int
    | Atom of byte * int
    | Cat  of Regex * Regex * int Set * int Set * bool
    | Or   of Regex * Regex * int Set * int Set * bool
    | Star of Regex * int Set * int Set
with
    static member op_Equality (reg,reg') = string reg = string reg'       
    
    member private R.IsSimple =
        match R with
        | Epsilon 
        | Terminal _
        | Atom _ -> true
        | Star (r,_,_) -> r.IsSimple
        | _ -> false

    member R.GetInterval =
        match R with
        | Or(Atom(a,_),Atom(b,_),_,_,_) when a = b-1uy -> Some(a,b)
        | Or(Atom(a,_), reg, _,_,_) ->
            reg.GetInterval
            |> Option.bind 
                (fun (min,max) -> 
                    if a = min-1uy then
                        Some(a,max) 
                    else None) 
        | Or(reg, Atom(a,_),_,_,_) ->
            reg.GetInterval
            |> Option.bind 
                (fun (min,max) -> 
                    if max = a-1uy then
                        Some(min,a) 
                    else None)

        | Or(reg, reg',_,_,_) ->
            match reg.GetInterval, reg'.GetInterval with
            | Some(min,max),Some(min',max') when max = min'-1uy -> Some(min,max')
            | Some(min,max),Some(min',max') when max' = min-1uy -> Some(min',max)
            | _ -> None

        | _ -> None
        
    override R.ToString() =
        match R with
        | reg when reg.GetInterval.IsSome -> 
            let pair = reg.GetInterval.Value
            $"['{char (fst pair)}'-'{char (snd pair)}']"

        | Or(Atom(a,_), reg,_,_,_) when reg.GetInterval.IsSome ->
            let pair = reg.GetInterval.Value
            $"['{char a}''{char (fst pair)}'-'{char (snd pair)}']"

        | Or(reg, Atom(a,_),_,_,_) when reg.GetInterval.IsSome ->
            let pair = reg.GetInterval.Value
            $"['{char (fst pair)}'-'{char (snd pair)}''{char a}']"

        | Or(reg,reg',_,_,_) when reg.GetInterval.IsSome && reg.GetInterval.IsSome ->
            let pair, pair' = reg.GetInterval.Value, reg'.GetInterval.Value
            $"['{char (fst pair)}'-'{char (snd pair)}''{char (fst pair')}'-'{char (snd pair')}']"

        | Terminal t -> $"{-t}#"
        | Atom(a, _) -> $"{char a}"
        | Cat(Epsilon, Epsilon, _,_,_)
        | Or(Epsilon, Epsilon, _,_,_) -> ""
        | Or(Epsilon, reg, _,_,_)
        | Or(reg, Epsilon, _,_,_) when reg.IsSimple -> $"{reg}?"
        | Or(Epsilon, reg, _,_,_)
        | Or(reg, Epsilon, _,_,_) -> $"({reg})?"
        | Or(Or _ as reg, reg',_,_,_) -> $"{reg}|{reg'}"
        | Or(reg,(Or _ as reg'),_,_,_) when reg.IsSimple -> $"{reg}|{reg'}"
        | Or(reg, reg',_,_,_) when reg.IsSimple -> $"{reg}|{reg'}"
        | Or(reg, reg',_,_,_) -> $"({reg})|({reg'})"
        | Star(reg,_,_) when reg.IsSimple -> $"{reg}*"
        | Cat(reg, Star(reg',_,_),_,_,_)
        | Cat(Star(reg, _,_), reg',_,_,_) when reg = reg' -> $"{reg}+"
        | Cat(reg, (Or _ as reg'),_,_,_) when reg.IsSimple -> $"{reg}({reg'})" 
        | Cat(reg, reg', _,_,_) when reg.IsSimple && reg'.IsSimple -> $"{reg}{reg'}"
        | Cat(reg, (Cat _ as reg'),_,_,_) when reg.IsSimple -> $"{reg}{reg'}"
        | Cat(reg, reg',_,_,_) -> $"{reg}{reg'}"
        | Star(reg,_,_) when reg.IsSimple -> $"{reg}*"
        | Star(reg,_,_) -> $"({reg})*"
        | Epsilon -> ""


let Nullable reg =
    match reg with
    | Star _ 
    | Epsilon -> true
    | Terminal _ 
    | Atom _ -> false
    | Or(_,_,_,_,n)
    | Cat(_,_,_,_,n) -> n


let First reg =
    match reg with
    | Epsilon -> set []
    | Terminal t -> set [t]
    | Atom(_, c) -> set [c]
    | Star(_, f, _)
    | Cat(_, _, f, _, _) 
    | Or(_, _, f, _, _) -> f

let Last reg =
    match reg with
    | Epsilon -> set []
    | Terminal t -> set [t]
    | Atom(_, c) -> set [c]
    | Star(_, _, f)
    | Cat(_, _, _, f, _) 
    | Or(_, _, _, f, _) -> f



let rec internal loop (flw: Set<int>[] byref) reg =    
    match reg with
    | Atom _
    | Terminal _
    | Epsilon _ -> ()
    | Or(reg1, reg2, _, _, _) -> 
        loop &flw reg1
        loop &flw reg2

    | Cat(c1, c2, _, _, _) ->
        loop &flw c1
        loop &flw c2
        for i in Last c1 do
            flw[i] <- flw[i] + First c2
    
    | Star(n, first, last) ->
        loop &flw n
        for i in last do
            flw[i] <- flw[i] + first
    
let Follow count reg =
    let mutable flws = [| for _ in 0 .. count -> set [] |]
    loop &flws reg
    flws

let Symbols reg =
    let rec loop reg =
        match reg with
        | Epsilon | Terminal _ -> set []
        | Atom(a,_) -> set [a]
        | Star(reg, _,_) -> loop reg
        | Or(reg1, reg2, _, _, _) 
        | Cat(reg1, reg2, _, _, _) -> loop reg1 + loop reg2

    loop reg
    |> Set.toArray

// not optimized
let PosOfSymbols reg =
    let symbols = Symbols reg
    let sop = 
        Array.map (fun a -> a, set []) symbols
        |> Map.ofArray

    let rec loop reg (sop: Map<_,_>) =
        match reg with
        | Atom(a, c) ->
            let pos' = sop[a]
            Map.add a (Set.add c pos') sop

        | Epsilon
        | Terminal _ -> sop
        | Or(reg1, reg2, _, _, _)
        | Cat(reg1, reg2, _, _, _) ->
            loop reg1 sop
            |> loop reg2

        | Star(reg, _,_) -> loop reg sop
    loop reg sop


let (<|>) reg1 reg2 =
    Or(reg1, reg2, First reg1 + First reg2, Last reg1 + Last reg2, Nullable reg1 || Nullable reg2)


let inline (.-.) a b =
    if a <= b then
        [| byte a .. byte b |]
        |> Array.map (fun r -> Atom(r, 0))
        |> Array.reduce (<|>)
    else
        Epsilon


let private (&) a1 a2 = Array.append a1 a2

let (.^.) a b =
    if a <= b then
        ([| 0uy .. byte a - 1uy |] & [| byte b + 1uy .. 255uy |]) // doublicats do nothing to the process
        |> Array.map (fun r -> Atom(r, 0))
        |> Array.reduce (<|>)
    else
        Epsilon

let (=>) reg1 reg2 =
    Cat(reg1, reg2, set [], set [], false)

let star reg = Star(reg, set [], set [])
let plus reg = reg => star reg
let maybe reg = reg <|> Epsilon

let inline private atom (a: 'a) =
    assert(uint a <= 255u)
    Atom(byte a, 0)


let AssignPosition reg =
    let rec loop pos reg =
        match reg with
        | Atom(a, _) -> Atom(a, pos), pos + 1
        | Cat(reg1, reg2, _,_,_) ->
            let reg1, pos = loop pos reg1
            let reg2, pos = loop pos reg2
            let fst = 
                if Nullable reg1 then
                    First reg1 + First reg2
                else
                    First reg1

            let flw =
                if Nullable reg2 then
                    Last reg1 + Last reg2
                else
                    Last reg2

            Cat(reg1, reg2, fst, flw, Nullable reg1 && Nullable reg2), pos
        | Or(reg1, reg2, _, _, _) ->
            let reg1, pos = loop pos reg1
            let reg2, pos = loop pos reg2
            Or(reg1, reg2, First reg1 + First reg2, Last reg1 + Last reg2, Nullable reg1 || Nullable reg2), pos
        | Star(reg,_,_) ->
            let reg, pos = loop pos reg
            Star(reg, First reg, Last reg), pos
        | _ -> reg, pos

    loop 0 reg

// sequencing regex for the bytepattern corosponding to the utf-8 encoding (ascii is a true subset)
let (!) (word: string) = 
    if word.Length = 0 then
        failwith "no pattern given"
    else
        System.Text.Encoding.UTF8.GetBytes word
        |> Seq.map atom 
        |> Seq.reduce (fun fst next -> fst => next) 


let lowercase       = 'a' .-. 'z'
let uppercase       = 'A' .-. 'Z'
let digit           = '0' .-. '9' <|> !"_"
let hexdigit        = digit <|> 'a' .-. 'f' <|> 'A' .-. 'F'
let letter          = lowercase <|> uppercase
let letterOrDigit   = letter <|> digit
let sign = maybe (!"+" <|> !"-")

let num = plus digit <|> (!"0x" => plus hexdigit)
let snum = sign => num

let floating = 
    let e = !"e" <|> !"E"
    let frac = star digit
    snum => !"." => frac => maybe (e => sign => plus digit)