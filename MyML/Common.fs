module Common

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Var = Var of string
with
    member this.AsString =
        let (Var(name)) = this
        name

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Operator =   Add
                | Subtract
                | Multiply
                | Divide
                | Equal
                | NotEqual
                | LessThan
                | LessThanOrEq
                | GreaterThan
                | GreaterThanOrEq
with
    member this.AsString =
        match this with
        | Add -> "+"
        | Subtract -> "-"
        | Multiply -> "*"
        | Divide -> "/"
        | Equal -> "="
        | NotEqual -> "!="
        | LessThan -> "<"
        | LessThanOrEq -> "<="
        | GreaterThan -> ">"
        | GreaterThanOrEq -> ">="

let mergeMap from to_ =
    Map.fold (fun t k v -> Map.add k v t) to_ from

let cons x xs = x :: xs