module Common

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Var = Var of string
with
    member this.AsString =
        let (Var(name)) = this
        name

type Signature =   SigLiteral of Var
                 | SigArrow of Signature * Signature

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

module State =
    type State<'s,'a> = State of ('s -> 'a * 's)
    type PlainBuilder() =
        member this.Zero() = failwith "?"
        member this.Return(a) = 
            fun s -> (a,s)
            |> State
        member this.Bind(State(get),f) =
            fun s ->
                let (a,s) = get s
                let (State(get')) = f a
                get' s
            |> State
    type Builder<'s>(initial: 's) =
        member this.Return(a) = 
            fun s -> (a,s)
            |> State
        member this.Bind(State(get),f) =
            fun s ->
                let (a,s) = get s
                let (State(get')) = f a
                get' s
            |> State
        member this.Run<'a>(s: State<'s,'a>) = 
            let (State(get)) = s
            get initial

    let yaruzo = new PlainBuilder()
    let withState a = new Builder<_>(a)

    let run s (State(get)) = get s
    let eval s state = run s state |> fst
    let exec s state = run s state |> snd

    let get<'a> : State<'a,'a> =
        fun s -> (s,s)
        |> State
    let set s = 
        fun _ -> ((),s)
        |> State
    let modify f =
        fun s ->
            ((),f s)
        |> State

    let (>>=) (State(get)) f =
         fun s ->
            let (a,s) = get s
            let (State(get')) = f a
            get' s
        |> State
    let (>>) s x = s >>= fun _ -> x

    let fmap f s =
        s >>= (fun x -> yaruzo{ return f x })
    let rec forM xs = yaruzo{
        match xs with
        | [] -> return []
        | x :: xs -> 
            let! x = x
            let! xs = forM xs
            return x :: xs
    }
    let rec foldM f s xs = 
        match xs with
        | [] -> yaruzo { return s }
        | x :: xs ->
            f s x
            >>= fun s -> foldM f s xs
    let rec forEachM f xs = foldM (fun _ x -> f x) () xs
    
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