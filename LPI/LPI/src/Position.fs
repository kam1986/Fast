module Position


open System


type [<Struct>] Pos =
    val Line: int
    val Offset: int
    val Absolut: int

    new(l, o, a) = { Line = l; Offset = o; Absolut = a }

    override P.ToString() = $"({P.Line}, {P.Offset})"
    static member op_Equality (p1: Pos, p2: Pos) = p1.Line = p2.Line && p1.Offset = p2.Offset
    
    interface IPos with member T.GetPos = T 

// used for indentation checking and easy access to position data
and IPos = abstract member GetPos: Pos

let PrintPos (pos: #IPos) = string pos

let GetPos (pos: #IPos) = pos.GetPos

let StartPos = Pos()

let Move (pos: Pos) steps = Pos(pos.Line, pos.Offset + steps, pos.Absolut + steps)

let Next pos = Move pos 1

let NewLine (pos: Pos) = Pos(pos.Line + 1, 0, pos.Absolut)
