module Token

open Position

open System.Text



type Token<'tag> =
    {
    Type: 'tag
    Start: Pos
    End: Pos
    Content: string
    }

    override T.ToString() = T.Type.ToString().ToLower()
     
    interface IPos with member T.GetPos = T.Start

let Token(tag, start, end', src) = { Type = tag; Start = start; End = end'; Content = src }

