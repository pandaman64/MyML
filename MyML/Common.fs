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

module Either =
    type Either<'a,'b> =   Left of 'a
                         | Right of 'b
    let map f either =
        match either with
        | Left(x) -> Left(x)
        | Right(x) -> Right(f x)
    let leftMap f either =
        match either with
        | Left(x) -> Left(f x)
        | Right(x) -> Right(x)
    let bind f either =
        match either with
        | Left(x) -> Left(x)
        | Right(x) -> f x
    let isLeft either = 
        match either with
        | Left(_) -> true
        | Right(_) -> false
    let isRight either =
        match either with
        | Left(_) -> false
        | Right(_) -> true
    let toSeq either =
        match either with
        | Left(_) -> Seq.empty
        | Right(x) -> Seq.singleton x
    let toList either =
        match either with
        | Left(_) -> []
        | Right(x) -> [x]
    let toOption either =
        match either with
        | Left(_) -> None
        | Right(x) -> Some(x)

module UnionFind =
    type Node<'a when 'a: equality> = { value: 'a; parent: Option<Node<'a>> ref; rank: int ref} 
    with
        member this.isRoot = (!this.parent).IsNone
        member this.updateParent parent = 
            this.parent := Some(parent)
    let rec Find (node: Node<_>) =
        if node.isRoot
        then
            node
        else
            let root = Find node
            node.updateParent root
            root
    let Union node node' =
        let root = Find node
        let root' = Find node'
        if !root.rank < !root'.rank
        then
            root.updateParent root'
        else if !root.rank > !root'.rank
        then
            root'.updateParent root
        else if root <> root'
        then
            root.updateParent root'
            root'.rank := !root'.rank + 1
    let Make value = { value = value; parent = ref None; rank = ref 0 }