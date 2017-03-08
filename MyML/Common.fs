module Common

type Var = Var of string

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Operator =   Add
                | Subtract
                | Multiply
                | Divide
with
    member this.AsString =
        match this with
        | Add -> "+"
        | Subtract -> "-"
        | Multiply -> "*"
        | Divide -> "/"

let mergeMap from to_ =
    Map.fold (fun t k v -> Map.add k v t) to_ from

let cons x xs = x :: xs