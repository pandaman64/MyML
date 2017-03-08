module Common

type Var = Var of string

let mergeMap from to_ =
    Map.fold (fun t k v -> Map.add k v t) to_ from