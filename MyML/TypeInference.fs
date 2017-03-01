﻿module TypeInference

type Var = Closure.Var
let Var = Closure.Var

type TyVar = TyVar of string

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Type =   TConstructor of Var
            | TVariable of TyVar
            | TArrow of Type * Type
            | TClosure of Type * Map<Var,Type>
with
    member this.freeTypeVariables =
        match this with
        | TConstructor(_) -> Set.empty
        | TVariable(var) -> Set.singleton var
        | TArrow(f,x) ->
            Set.union f.freeTypeVariables x.freeTypeVariables
        | TClosure(t,env) ->
            Map.toSeq env
            |> Seq.map snd
            |> Seq.map (fun t -> t.freeTypeVariables)
            |> Seq.append [t.freeTypeVariables]
            |> Set.unionMany
    member this.Apply subst =
        match this with
        | TVariable(var) ->
            match Map.tryFind var subst with
            | None -> this
            | Some(type_) -> type_
        | TArrow(f,x) -> TArrow(f.Apply subst,x.Apply subst)
        | TClosure(t,env) ->
            let t = t.Apply subst
            let env = env
                      |> Map.map (fun _ t -> t.Apply subst)
            TClosure(t,env)
        | TConstructor(_) -> this

let intType = TConstructor(Var("Int"))
let boolType = TConstructor(Var("Bool"))
let newTyVar =
    let mutable counter = 0
    let func name =
        counter <- counter + 1
        TVariable(TyVar(sprintf "%s%d" name counter))
    func

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Scheme = {boundVariables: Set<TyVar>; type_: Type}
with
    member this.freeTypeVariables =
        let {boundVariables = vars; type_ = t} = this
        t.freeTypeVariables - vars
    member this.Apply subst =
        let {boundVariables = vars; type_ = t} = this
        let innerSubst = Set.fold (fun subst var -> Map.remove var subst) subst vars
        { boundVariables = vars; type_ = t.Apply innerSubst}
    static member fromType type_ =
        {boundVariables = Set.empty; type_ = type_}

type TypeEnv = TypeEnv of Map<Var,Scheme>
with
    member this.Add name scheme =
        let (TypeEnv(env)) = this
        TypeEnv(Map.add name scheme env)
    member this.freeTypeVariables =
        let (TypeEnv(env)) = this
        env
        |> Map.toSeq
        |> Seq.map snd
        |> Seq.map (fun scheme -> scheme.freeTypeVariables)
        |> Set.unionMany
    member this.Apply subst = 
        let (TypeEnv(env)) = this
        env
        |> Map.map (fun _ scheme -> scheme.Apply subst) 
        |> TypeEnv
    member this.Merge other =
        let (TypeEnv(this)) = this
        let (TypeEnv(other)) = other
        let this = Map.fold (fun this name scheme -> Map.add name scheme this) this other
        TypeEnv(this)

type Substitution = Map<TyVar,Type>

let generalize (env: TypeEnv) (type_: Type): Scheme =
    let vars = type_.freeTypeVariables - env.freeTypeVariables
    {boundVariables = vars; type_ = type_}

let instantiate (scheme: Scheme): Type =
    let {boundVariables = vars; type_ = type_} = scheme
    let substitution = vars
                       |> Set.map (fun v -> v,newTyVar "t")
                       |> Map.ofSeq
    type_.Apply substitution

let emptySubstitution: Substitution = Map.empty

let composeSubstitution (s1: Substitution) (s2: Substitution): Substitution =
    Map.fold (fun s k v -> Map.add k v s) s1 s2
let composeSubstitutionMany (xs: Substitution seq): Substitution =
    Seq.fold composeSubstitution emptySubstitution xs

let varBind (var: TyVar) (t: Type): Substitution =
    if t.freeTypeVariables.Contains var 
    then
        failwithf "Occur check failed: %A -> %A" var t
    else
        Map.add var t emptySubstitution

let rec unify (t1: Type) (t2: Type): Substitution =
    match t1,t2 with
    | TVariable(v),_ -> varBind v t2
    | _,TVariable(v) -> varBind v t1
    | TConstructor(c1),TConstructor(c2) when c1.Equals c2 -> emptySubstitution
    | TArrow(f1,x1),TArrow(f2,x2) ->
        let s1 = unify f1 f2
        let s2 = unify (x1.Apply s1) (x2.Apply s1)
        composeSubstitution s1 s2
    | TClosure(t1,env1),TClosure(t2,env2) ->
        let folder subst name t =
            let s = 
                match env2.TryFind name with
                | None -> emptySubstitution
                | Some(t') -> unify t t'
            composeSubstitution subst s
        let s1 = unify t1 t2
        let sEnv = env1
                   |> Map.fold folder emptySubstitution
        composeSubstitution s1 sEnv
    | TClosure(t,env),_ -> unify t t2
    | _,TClosure(t,env) -> unify t1 t    
    | _ -> failwithf "type mismatch between %A and %A" t1 t2

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Expr =   Literal of int
            | ExternRef of Var
            | Alias of Var * TypedExpr * TypedExpr
            | AliasRec of Var * TypedExpr * TypedExpr
            | Apply of TypedExpr * TypedExpr
            | ApplyClosure of TypedExpr * Map<Var,TypedExpr> 
            | If of TypedExpr * TypedExpr * TypedExpr
with
    member this.Apply' subst: Expr =
        match this with
        | Literal(_) -> this
        | ExternRef(_) -> this
        | Alias(name,value,body) -> Alias(name,value.Apply subst,body.Apply subst)
        | AliasRec(name,value,body) -> AliasRec(name,value.Apply subst,body.Apply subst)
        | Apply(f,x) -> Apply(f.Apply subst,x.Apply subst)
        | ApplyClosure(cls,applications) -> ApplyClosure(cls.Apply subst,applications)
        | If(cond,ifTrue,ifFalse) -> If(cond.Apply subst,ifTrue.Apply subst,ifFalse.Apply subst)
and
    [<StructuredFormatDisplayAttribute("{AsString}")>]
    TypedExpr = {value: Expr; type_: Type}
with
    member this.Apply subst: TypedExpr =
        {value = this.value.Apply' subst; type_ = this.type_.Apply subst}

[<StructuredFormatDisplayAttribute("{AsString}")>]
type SchemedExpr = {value: Expr; type_: Scheme}

type Expr
with
    member this.WithType (type_: Type): TypedExpr =
        {value = this; type_ = type_}

type Function = {argument: Var; body: TypedExpr}
with
    member this.Apply subst: Function = 
        {argument = this.argument; body = this.body.Apply subst}
type TypedFunction = {value: Function; type_: Scheme}
type TypedClosure = Closure of Var * TypedFunction * Map<Var,Type>

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Declaration =   FreeValue of Var * SchemedExpr
                   | FreeFunction of Var * TypedFunction
                   | FreeRecFunction of Var * TypedFunction
                   | ClosureDecl of TypedClosure
                   | ClosureRecDecl of TypedClosure
with
    member this.Name =
        match this with
        | FreeValue(name,_) -> name
        | FreeFunction(name,_) -> name
        | FreeRecFunction(name,_) -> name
        | ClosureDecl(Closure(name,_,_)) -> name
        | ClosureRecDecl(Closure(name,_,_)) -> name
    member this.Scheme =
        match this with
        | FreeValue(_,expr) -> expr.type_
        | FreeFunction(_,f) -> f.type_
        | FreeRecFunction(_,f) -> f.type_
        | ClosureDecl(Closure(_,f,_)) -> f.type_
        | ClosureRecDecl(Closure(_,f,_)) -> f.type_

type Type
with
    member this.AsString =
        match this with
        | TConstructor(AlphaTransform.Var(name)) -> name
        | TVariable(TyVar(name)) -> name
        | TArrow(f,x) -> sprintf "%A -> %A" f x
        | TClosure(t,captured) -> 
            let capturedString = 
                Map.toSeq captured
                |> Seq.map (fun (AlphaTransform.Var(name),type_) -> sprintf "%s => %A" name type_)
                |> String.concat " "
            sprintf "%A {%s}" t capturedString

type Scheme
with
    member this.AsString = 
        let boundString =   
            Set.toSeq this.boundVariables
            |> Seq.map (fun (TyVar(name)) -> sprintf "FA %s." name)
            |> String.concat ""
        sprintf "%s%A" boundString this.type_

type Expr
with
    member this.AsString =
        match this with
        | Literal(x) -> sprintf "%d" x
        | ExternRef(AlphaTransform.Var(name)) -> name
        | Alias(AlphaTransform.Var(name),value,body) ->
            sprintf "alias %s = %A in %A" name value body
        | AliasRec(AlphaTransform.Var(name),value,body) ->
            sprintf "alias rec %s = %A in %A" name value body
        | Apply(f,x) -> sprintf "(%A %A)" f x
        | ApplyClosure(f,applications) -> 
            let applicationString = 
                Map.toSeq applications
                |> Seq.map (fun (AlphaTransform.Var(name),expr) -> sprintf "%s => %A" name expr)
                |> String.concat " "
            sprintf "[%A %s]" f applicationString
        | If(cond,ifTrue,ifFalse) ->
            sprintf "if %A then %A else %A" cond ifTrue ifFalse

type TypedExpr
with
    member this.AsString =
        sprintf "<%A: %A>" this.value this.type_

type SchemedExpr
with
    member this.AsString =
        sprintf "<%A: %A>" this.value this.type_

type Declaration
with
    member this.AsString =
        match this with
        | FreeValue(AlphaTransform.Var(name),value) ->
            sprintf "value %s = %A" name value
        | FreeFunction(AlphaTransform.Var(name),f) -> 
            sprintf "function <%s: %A> %A = %A" name f.type_ f.value.argument f.value.body
        | FreeRecFunction(AlphaTransform.Var(name),f) -> 
            sprintf "function rec <%s: %A> %A = %A" name f.type_ f.value.argument f.value.body
        | ClosureDecl(Closure(AlphaTransform.Var(name),f,captured)) ->
            let capturedString =
                Map.toSeq captured
                |> Seq.map (fun (AlphaTransform.Var(name),type_) -> sprintf "%s => %A" name type_)
                |> String.concat " "
            sprintf "closure <%s: %A> %A {%s} = %A" name f.type_ f.value.argument capturedString f.value.body
        | ClosureRecDecl(Closure(AlphaTransform.Var(name),f,captured)) ->
            let capturedString =
                Map.toSeq captured
                |> Seq.map (fun (AlphaTransform.Var(name),type_) -> sprintf "%s => %A" name type_)
                |> String.concat " "
            sprintf "closure rec <%s: %A> %A {%s} = %A" name f.type_ f.value.argument capturedString f.value.body

let rec inferExpr (env: TypeEnv) (expr: Closure.Expr): Substitution * TypedExpr =
    match expr with
    | Closure.Literal(x) -> emptySubstitution,Literal(x).WithType intType
    | Closure.ExternRef(name) -> 
        let expr = ExternRef(name)
        let (TypeEnv(env)) = env
        match env.TryFind name with
        | None ->
            printfn "%A not found in the environment: %A" name env
            emptySubstitution,expr.WithType (newTyVar "t")
        | Some(scheme) ->
            emptySubstitution,expr.WithType (instantiate scheme)
    | Closure.Apply(f,x) ->
        let sf,f = inferExpr env f
        let sx,x = inferExpr (env.Apply sf) x
        let t = newTyVar "t"
        let subst = unify (f.type_.Apply sx) (TArrow(x.type_,t))
        composeSubstitutionMany [sf; sx; subst],Apply(f.Apply subst,x.Apply subst).WithType (t.Apply subst)
    | Closure.If(cond,ifTrue,ifFalse) ->
        let sc,cond = inferExpr env cond
        let sc2 = unify cond.type_ boolType
        let subst = composeSubstitution sc sc2
        let st,ifTrue = inferExpr (env.Apply subst) ifTrue
        let subst = composeSubstitution subst st
        let sf,ifFalse = inferExpr(env.Apply subst) ifFalse
        let subst = composeSubstitution subst sf
        let subst = unify (ifTrue.type_.Apply subst) (ifFalse.type_.Apply subst)
        let cond = cond.value.WithType (cond.type_.Apply subst)
        let ifTrue = ifTrue.value.WithType (ifTrue.type_.Apply subst)
        let ifFalse = ifFalse.value.WithType (ifFalse.type_.Apply subst)
        subst,If(cond,ifTrue,ifFalse).WithType ifTrue.type_
    | Closure.Alias(name,value,body) ->
        let sv,value = inferExpr env value
        let env = (env.Apply sv).Add name (generalize (env.Apply sv) value.type_)
        let sb,body = inferExpr env body
        let subst = composeSubstitution sv sb
        subst,Alias(name,value.Apply subst,body.Apply subst).WithType (body.type_.Apply subst)
    | Closure.AliasRec(name,value,body) ->
        let valueType = newTyVar "t"
        let env = env.Add name (Scheme.fromType valueType)
        let sv,value = inferExpr env value
        let env = (env.Apply sv).Add name (generalize (env.Apply sv) value.type_)
        let sb,body = inferExpr env body
        let subst = composeSubstitution sv sb
        subst,AliasRec(name,value.Apply subst,body.Apply subst).WithType (body.type_.Apply subst)
    | Closure.ApplyClosure(cls,applications) ->
        let folder (subst,applications) name expr =
            let s,expr = inferExpr (env.Apply subst) expr
            composeSubstitution subst s,Map.add name expr applications
        let subst,applications = Map.fold folder (emptySubstitution,Map.empty) applications
        let env = env.Apply subst
        let sc,cls = inferExpr env cls
        let subst = composeSubstitution subst sc
        let su = unify cls.type_ (TClosure(newTyVar "t",applications |> Map.map (fun _ expr -> expr.type_.Apply subst)))
        let subst = composeSubstitution subst su

        // the type of closure application is the underlying type of the closure
        let type_ = match cls.type_.Apply subst with
                    | TClosure(type_,_) -> type_
                    | _ -> failwith "must be closure"
        subst,ApplyClosure(cls.Apply subst,applications).WithType type_

let inferDecl (env: TypeEnv) (decl: Closure.Declaration): Substitution * Declaration =
    match decl with
    | Closure.FreeValue(name,value) ->
        let s,value = inferExpr env value
        let (schemed: SchemedExpr) = {value = value.value; type_ = generalize (env.Apply s) value.type_} 
        s,FreeValue(name,schemed)
    | Closure.FreeFunction(name,f) ->
        let argType = newTyVar "t"
        let innerEnv = env.Add f.argument (Scheme.fromType argType)
        let s,body = inferExpr innerEnv f.body
        let thisScheme = 
            let thisType = TArrow(argType.Apply s,body.type_.Apply s)
            generalize (env.Apply s) thisType
        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme}
        s,FreeFunction(name,value)
    | Closure.FreeRecFunction(name,f) ->
        let thisType = newTyVar "t"
        let argType = newTyVar "t"
        let env = 
            let env = env.Add f.argument (Scheme.fromType argType)
            env.Add name (Scheme.fromType thisType)
        let s1,body = inferExpr env f.body
        let s2 = unify thisType (TArrow(argType,body.type_))
        let s = composeSubstitution s1 s2
        let thisScheme = generalize (env.Apply s) thisType
        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme}  
        s,FreeRecFunction(name,value)
    | Closure.ClosureDecl(Closure.Closure(name,f,capturedVariables)) ->
        let argType = newTyVar "t"
        let captured = capturedVariables
                       |> Set.map (fun v -> v,newTyVar "t")
                       |> Map.ofSeq
        let capturedEnv = Map.map (fun _ t -> Scheme.fromType t) captured
                          |> TypeEnv
        let innerEnv = (env.Merge capturedEnv).Add f.argument (Scheme.fromType argType)
        let s,body = inferExpr innerEnv f.body
        let captured = captured
                       |> Map.map (fun _ t -> t.Apply s)
        let thisScheme = 
            let thisType = TArrow(argType.Apply s,body.type_.Apply s)
            
            let closureType = TClosure(thisType.Apply s,captured)
            generalize (env.Apply s) closureType
        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme}
        s,ClosureDecl(Closure(name,value,captured))
    | Closure.ClosureRecDecl(Closure.Closure(name,f,capturedVariables)) ->
        let thisType = newTyVar "t"
        let argType = newTyVar "t"
        let captured = capturedVariables
                       |> Set.map (fun v -> v,newTyVar "t")
                       |> Map.ofSeq
        let env = 
            let env = env.Add f.argument (Scheme.fromType argType)
            let env = env.Add name (Scheme.fromType thisType)
            let capturedEnv = Map.map (fun _ t -> Scheme.fromType t) captured
                              |> TypeEnv
            env.Merge capturedEnv
        let s1,body = inferExpr env f.body
        let captured = captured
                       |> Map.map (fun _ t -> t.Apply s1)
        let closureType =
            let thisType = TArrow(argType.Apply s1,body.type_.Apply s1)
            TClosure(thisType.Apply s1,captured)
        let s2 = unify thisType closureType
        let s = composeSubstitution s1 s2
        let thisScheme = generalize (env.Apply s) thisType
        // probably `s` should be applied to body.type_
        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme}
        s,ClosureRecDecl(Closure(name,value,captured))

let inferDecls (env: TypeEnv) (decls: Closure.Declaration list): Declaration list =
    let folder (env,decls) decl =
        let s,decl = inferDecl env decl
        (env.Apply s).Add decl.Name decl.Scheme,decl :: decls
    let _,decls = List.fold folder (env,[]) decls
    // keep the ordering of declarations
    List.rev decls