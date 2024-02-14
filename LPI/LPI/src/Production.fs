module Production

[<Struct>]
type Symbol<'prod, 'token> =
    | NoneTerminal of p: 'prod
    | Terminal of t: 'token
    | End


let (!) token = Symbol.Terminal token
let (!!) production = Symbol.NoneTerminal production


type Rule<'prod, 'token> = Rule of Symbol<'prod,'token> array


type Production<'prod, 'token> = Production of Rule<'prod,'token> array


