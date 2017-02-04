﻿module Program

open FParsec
open Parser

type Var = Var of string

type Expr' =   Num of int
             | VarRef of Var
             | Fun of Var * Expr'
             | Let' of Var * Expr' * Expr'
             | LetRec' of Var * Expr' * Expr'
             | Apply' of Expr' * Expr'
             | If' of Expr' * Expr' * Expr'

module Environment =
    type Environment = Map<Var,Expr'> list
    let empty:Environment = [Map.empty]
    let push (env:Environment) = Map.empty :: env
    let pop (env:Environment) = List.tail env
    let add v e (env:Environment) = 
        match env with
        | [] -> failwith "no environment"
        | e' :: es -> (Map.add v e e') :: es
    let rec tryFind v (env:Environment) = 
        match env with
        | [] -> None
        | e :: es -> 
            match Map.tryFind v e with
            | None -> tryFind v es
            | some -> some

let alpha_transform expr =
    let rec impl env expr =
        match expr with
        | Literal(x) -> Num(x)
        | If(cond,ifTrue,ifFalse) -> If'(impl env cond,impl env ifTrue,impl env ifFalse)
        | Apply(f,xs) -> 
            match xs with
            | [] -> impl env f
            | xs ->
                let rec impl' f xs =
                    match xs with
                    | [] -> f
                    | x::xs -> impl' (Apply'(f,x)) xs 
                impl' (impl env f) (List.map (impl env) xs)
        | Identifier(name) -> 
            match Environment.tryFind (Var(name)) env with
            //| None -> printfn "variable %s not found in %A" name env;failwith "variable not found"
            | None -> printfn "variable not found '%s' in %A.\nType information of '%s' must be supplied later." name env name; VarRef(Var(name))
            | Some(e) -> e
        | Let(thisName,argName,value,inValue) -> 
            match argName with
            | None -> //alias
                let value' = impl env value
                let newEnv = Environment.add (Var(thisName)) value' env
                Let'(Var(thisName),value',impl newEnv inValue)
            | Some(x) -> //function definition
                let var = Var(x)
                let innerEnv = Environment.add var (VarRef(var)) (Environment.push env)
                let value' = impl innerEnv value
                let this = Fun(var,value')
                let newEnv = Environment.add (Var(thisName)) this env
                Let'(Var(thisName),this,impl newEnv inValue)
        | LetRec(thisName,argName,value,inValue) ->
            let varThis = Var(thisName)
            let env = Environment.add varThis (VarRef(varThis)) env
            match argName with
            | None -> //alias
                let value' = impl env value
                LetRec'(Var(thisName),value',impl env inValue)
            | Some(x) -> //function definition
                let var = Var(x)
                let innerEnv = Environment.add var (VarRef(var)) (Environment.push env)
                let value' = impl innerEnv value
                let this = Fun(var,value')
                LetRec'(Var(thisName),this,impl env inValue)
    impl Environment.empty expr

type TVar = TV of string

type Type =   TVar of TVar 
            | TCon of string
            | TArrow of Type * Type

let intType = TCon "Int"
let boolType = TCon "Bool"

type Scheme = Forall of TVar list * Type

type TypeEnv = TypeEnv of Map<Var,Scheme>

let extend (TypeEnv env) (x,s) = TypeEnv(Map.add x s env)

type Subst = Map<TVar,Type>

type Type with
    member this.freeTypeVariables =
        match this with
        | TCon(_) -> Set.empty
        | TVar(var) -> Set.singleton var
        | TArrow(f,x) -> Set.union f.freeTypeVariables x.freeTypeVariables
    member this.apply (subst: Subst) = 
        match this with
        | TVar(var) ->
            match subst.TryFind var with
            | None -> TVar(var)
            | Some(t) -> t
        | TArrow(f,x) ->
            TArrow(f.apply subst,x.apply subst)
        | _ -> this

type Scheme with
    member this.freeTypeVariables =
        match this with
        | Forall(vars,t) -> t.freeTypeVariables - Set.ofList vars
    member this.apply (subst: Subst) =
        match this with
        | Forall(vars,t) -> 
            let newSubst = List.fold (fun ns i -> Map.remove i ns) subst vars
            let newType = t.apply newSubst
            Forall(vars,newType)

type TypeEnv with
    member this.remove var =
        match this with
        | TypeEnv(scheme) -> TypeEnv(scheme.Remove var)
    member this.freeTypeVariables =
        match this with
        | TypeEnv(scheme) ->
            Seq.map snd (Map.toSeq scheme)
            |> Seq.map (fun sc -> sc.freeTypeVariables)
            |> Set.unionMany
    member this.apply (subst: Subst) =
        match this with
        | TypeEnv(scheme) ->
            let newScheme = Map.map (fun k (v: Scheme) -> v.apply subst) scheme
            TypeEnv(newScheme)

let unionMap<'k,'v when 'k: comparison> (m1: Map<'k,'v>) (m2: Map<'k,'v>):Map<'k,'v> =
    if m1.Count = 0 then m2
    else
        if m2.Count = 0 then m1
        else
            Map.fold (fun m2' k v -> Map.add k v m2') m2 m1

let singletonMap<'k,'v when 'k: comparison> (k: 'k) (v: 'v) : Map<'k,'v> =
    Map.add k v Map.empty

let nullSubst:Subst = Map.empty
//s2にs1を適用してからマージ
let composeSubst (s1: Subst) (s2: Subst) =
    let news2 = Map.map (fun k (t: Type) -> t.apply s1) s2
    unionMap news2 s1

//stateful
let newTyVar =
    let nextIndex = ref 1
    fun name ->
        let name = sprintf "%s@%d" name !nextIndex
        nextIndex := !nextIndex + 1
        TVar(TV(name))

//replace all free type variables which don't appear in outer environment with ∀
let generalize (env: TypeEnv) (t: Type) =
    Forall(Set.toList (env.freeTypeVariables - t.freeTypeVariables),t)
//instantiate fresh new type variable for each ∀
let instantiate (ts: Scheme) =
    match ts with
    | Forall(vars,t) ->
        let newVars = List.map (fun _ -> newTyVar "a") vars
        let mapping = Map.ofList (List.zip vars newVars)
        t.apply mapping

//bind a name to type
let varBind (var: TVar) (t: Type): Subst =
    match t with
    | TVar(var) -> Map.empty //?
    | _ when t.freeTypeVariables.Contains var ->
        failwithf "Occur check failed: %A -> %A" var t
    | _ -> singletonMap var t

let rec unify (t1: Type) (t2: Type): Subst =
    match t1,t2 with
    | TCon(x),TCon(y) when x = y -> Map.empty
    | TCon(x),TCon(y) -> failwithf "concrete type %s doesn't match %s" x y
    | TArrow(x1,y1),TArrow(x2,y2) ->
        let s1 = unify x1 x2
        let s2 = unify (y1.apply s1) (y2.apply s1)
        composeSubst s1 s2
    | TVar(var), t -> varBind var t
    | t, TVar(var) -> varBind var t
    | _ -> failwithf "not implemented: %A vs %A" t1 t2

//型推論関数
let rec infer (env: TypeEnv) (expr: Expr') : Subst * Type =
    match expr with
    | Num(_) -> Map.empty,intType
    | VarRef(name) -> 
        match env with
        | TypeEnv(env) -> 
            match env.TryFind name with
            | None -> failwithf "variable '%A' not found in environment %A" name env
            | Some(scheme) -> 
                let t = instantiate scheme
                Map.empty, t
    | Fun(arg,body) -> 
        match env with
        | TypeEnv(env) ->
            let tv = newTyVar "a.arg"
            //replace outer type variable named {arg} with fresh new variable
            let innerEnv = TypeEnv(Map.add arg (Forall([],tv)) env)
            let subst, t = infer innerEnv body
            subst, TArrow(tv.apply subst,t)
    | Apply'(f,x) -> 
        let tv = newTyVar "a.ret"
        let s1, t1 = infer env f
        let s2, t2 = infer (env.apply s1) x
        let s3 = unify (t1.apply s2) (TArrow(t2,tv)) //?
        composeSubst (composeSubst s3 s2) s1, tv.apply s3
    | Let'(name,this,body) -> 
        let s1, t1 = infer env this
        let thisScheme = generalize (env.apply s1) t1
        match env with
        | TypeEnv(env') -> 
            let bodyEnv = TypeEnv(Map.add name thisScheme env')
            let s2, t2 = infer (bodyEnv.apply s1) body
            composeSubst s1 s2, t2
    | LetRec'(name,this,body) -> 
        //first infer this type
        let tv = newTyVar "a"
        let env = match env with
                  | TypeEnv(env) -> TypeEnv(Map.add name (Forall([],tv)) env)
        let s1, t1 = infer env this
        let thisScheme = generalize (env.apply s1) t1

        //then replace this with inferred type
        let bodyEnv = match env with
                      | TypeEnv(env) -> TypeEnv(Map.add name thisScheme env)
        let s2, t2 = infer (bodyEnv.apply s1) body
        composeSubst s1 s2, t2
    | If'(cond,ifTrue,ifFalse) -> 
        let sCond, tCond = infer env cond
        let sCond = unify tCond boolType
        let newEnv = env.apply sCond
        let sTrue, tTrue = infer newEnv ifTrue
        let sFalse, tFalse = infer newEnv ifFalse
        let s = unify tTrue tFalse
        let subst = Seq.fold composeSubst nullSubst [sCond;sTrue;sFalse;s;]
        subst,tTrue

let inferAll (env: TypeEnv) (expr: Expr') : Type =
    let s, t = infer env expr
    t.apply s

[<EntryPoint>]
let main argv = 
    (*let str = """
        let rec fact x = 
            if eq x 0 then 
                1
            else
                fact (minus x 1);
        let rec fib x = 
            if lt x 2 then
                1
            else
                (plus (fib (minus x 1) (minus x 2)));
        let v = 10 in
        let fa = fact v in
        let fb = fib v in
        minus fa fb
        """
    printfn "%s" str*)
    (*match run pprogram str with
    | Success(result,_,_) -> 
        printfn "%A" result;
    | Failure(msg,_,_) -> printfn "%s" msg*)
    (*let source = """
        let x = 0 in
        let y = 1 in
        let id x = x in
        let const x = 
            let f y = x in
            f in
        id (const y x)"""*)
    let source = """
        let rec fib x =
            if (eq x 0) then 1
            else (multiply x (fib (minus x 1))) in
        fib"""
    printfn "%s" source
    match run pexpr source with
    | Success(result,_,_) ->
        //printfn "%A" result;
        let result = alpha_transform result
        //printfn "%A" result;
        let primitiveEnv =
            let plus = (Var("plus")), (Forall([],TArrow(intType,TArrow(intType,intType))))
            let minus = (Var("minus")), (Forall([],TArrow(intType,TArrow(intType,intType))))
            let multiply = (Var("multiply")), (Forall([],TArrow(intType,TArrow(intType,intType))))
            let eq = (Var("eq")), (Forall([],TArrow(intType,TArrow(intType,boolType))))
            let env = Map.ofList [plus;minus;multiply;eq]
            TypeEnv(env)
        printfn "%A" (infer primitiveEnv result)
    | Failure(msg,_,_) -> printfn "%s" msg
    0 // return an integer exit code
