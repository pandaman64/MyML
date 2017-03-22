module Interpreter

open Common

type Closure = { name: Var; application: Map<Var,Value> }
and
     Value =   Bool of bool
             | Int of int
             | Fun of Var
             | Closure of Closure  

type Environment = { stack: Value list }
with
    member this.Push value = 
        { stack = value :: this.stack }
    member this.Pop =
        match this.stack with
        | [] -> failwith "empty stack"
        | v :: vs -> v,{ stack = vs }

let rec evalExpr (expr: TypeInference.TypedExpr) (env: Environment): Environment =
    match expr.value with
    | TypeInference.Literal(x) -> env.Push (Int(x))
