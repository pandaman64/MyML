module TypeInference

open Common
open Either

type TyVar = TyVar of string

type RecordType = RecordType of Map<Var,Type>
and
    [<StructuredFormatDisplayAttribute("{AsString}")>]
    Type =   TConstructor of Var
            | TVariable of TyVar
            | TArrow of Type * Type
            | TClosure of Type * Map<Var,Type>
            | TRecord of RecordType
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
        | TRecord(RecordType(fields)) ->
            Map.toSeq fields
            |> Seq.map snd
            |> Seq.map (fun type_ -> type_.freeTypeVariables)
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
        | TRecord(RecordType(fields)) ->
            fields
            |> Map.map (fun _ type_ -> type_.Apply subst)
            |> RecordType
            |> TRecord

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
    let s1 = s1 |> Map.map (fun k v -> v.Apply s2)
    Map.fold (fun s k v -> Map.add k v s) s1 s2
let composeSubstitutionMany (xs: Substitution seq): Substitution =
    Seq.fold composeSubstitution emptySubstitution xs

let varBind (var: TyVar) (t: Type): Substitution =
    match t with
    | TVariable(var') when var = var' -> emptySubstitution
    | _ when t.freeTypeVariables.Contains var -> failwithf "Occur check failed: %A -> %A" var t
    | _ -> Map.add var t emptySubstitution

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
            | Apply of TypedExpr * TypedExpr list
            | ApplyClosure of TypedExpr * Map<Var,TypedExpr> 
            | If of TypedExpr * TypedExpr * TypedExpr
            | BinOp of TypedExpr * Operator * TypedExpr
            | RecordLiteral of Map<Var,TypedExpr>
            | RecordAccess of TypedExpr * Var
with
    member this.Apply' subst: Expr =
        match this with
        | Literal(_) -> this
        | ExternRef(_) -> this
        | Alias(name,value,body) -> Alias(name,value.Apply subst,body.Apply subst)
        | AliasRec(name,value,body) -> AliasRec(name,value.Apply subst,body.Apply subst)
        | Apply(f,xs) -> Apply(f.Apply subst,xs |> List.map (fun x -> x.Apply subst))
        | ApplyClosure(cls,applications) -> ApplyClosure(cls.Apply subst,applications)
        | If(cond,ifTrue,ifFalse) -> If(cond.Apply subst,ifTrue.Apply subst,ifFalse.Apply subst)
        | BinOp(lhs,op,rhs) -> BinOp(lhs.Apply subst,op,rhs.Apply subst)
        | RecordLiteral(fields) ->
            fields
            |> Map.map (fun _ expr -> expr.Apply subst)
            |> RecordLiteral
        | RecordAccess(expr,name) -> RecordAccess(expr.Apply subst,name)
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

type Function = {argument: Var list; body: TypedExpr}
with
    member this.Apply subst: Function = 
        {argument = this.argument; body = this.body.Apply subst}
type TypedFunction = {value: Function; type_: Scheme}
type TypedClosure = Closure of Var * TypedFunction * Map<Var,Type>

type TypeDecl =   Record of Map<Var,Type>
                | TyAlias of Type

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Declaration =   FreeValue of Var * SchemedExpr
                   | FreeFunction of Var * TypedFunction
                   | FreeRecFunction of Var * TypedFunction
                   | ClosureDecl of TypedClosure
                   | ClosureRecDecl of TypedClosure
                   | TypeDecl of Var * TypeDecl
with
    member this.Name =
        match this with
        | FreeValue(name,_) -> name
        | FreeFunction(name,_) -> name
        | FreeRecFunction(name,_) -> name
        | ClosureDecl(Closure(name,_,_)) -> name
        | ClosureRecDecl(Closure(name,_,_)) -> name
        | TypeDecl(name,_) -> name
    member this.Scheme =
        match this with
        | FreeValue(_,expr) -> expr.type_
        | FreeFunction(_,f) -> f.type_
        | FreeRecFunction(_,f) -> f.type_
        | ClosureDecl(Closure(_,f,_)) -> f.type_
        | ClosureRecDecl(Closure(_,f,_)) -> f.type_
        | TypeDecl(_,_) -> failwith "okashii"

type Type
with
    member this.AsString =
        match this with
        | TConstructor(Var(name)) -> name
        | TVariable(TyVar(name)) -> name
        | TArrow(f,x) -> sprintf "%A -> %A" f x
        | TClosure(t,captured) -> 
            let capturedString = 
                Map.toSeq captured
                |> Seq.map (fun (Var(name),type_) -> sprintf "%s => %A" name type_)
                |> String.concat " "
            sprintf "%A {%s}" t capturedString
        | TRecord(RecordType(fields)) ->
            let fieldsString = 
                Map.toSeq fields
                |> Seq.map (fun (Var(name),type_) -> sprintf "%s: %A" name type_)
                |> String.concat "; "
            sprintf "{ %s }" fieldsString

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
        | ExternRef(Var(name)) -> name
        | Alias(Var(name),value,body) ->
            sprintf "alias %s = %A in %A" name value body
        | AliasRec(Var(name),value,body) ->
            sprintf "alias rec %s = %A in %A" name value body
        | Apply(f,x) -> sprintf "(%A %A)" f x
        | ApplyClosure(f,applications) -> 
            let applicationString = 
                Map.toSeq applications
                |> Seq.map (fun (Var(name),expr) -> sprintf "%s => %A" name expr)
                |> String.concat " "
            sprintf "[%A %s]" f applicationString
        | If(cond,ifTrue,ifFalse) ->
            sprintf "if %A then %A else %A" cond ifTrue ifFalse
        | BinOp(lhs,op,rhs) -> sprintf "(%A %A %A)" lhs op rhs
        | RecordLiteral(fields) ->
            let fieldsString =
                Map.toSeq fields
                |> Seq.map (fun (Var(name),value) -> sprintf "%s = %A" name value)
                |> String.concat "; "
            sprintf "{ %s }" fieldsString
        | RecordAccess(obj,Var(name)) -> sprintf "(%A).%s" obj name 

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
        | FreeValue(Var(name),value) ->
            sprintf "value %s = %A" name value
        | FreeFunction(Var(name),f) -> 
            sprintf "function <%s: %A> %A = %A" name f.type_ f.value.argument f.value.body
        | FreeRecFunction(Var(name),f) -> 
            sprintf "function rec <%s: %A> %A = %A" name f.type_ f.value.argument f.value.body
        | ClosureDecl(Closure(Var(name),f,captured)) ->
            let capturedString =
                Map.toSeq captured
                |> Seq.map (fun (Var(name),type_) -> sprintf "%s => %A" name type_)
                |> String.concat " "
            sprintf "closure <%s: %A> %A {%s} = %A" name f.type_ f.value.argument capturedString f.value.body
        | ClosureRecDecl(Closure(Var(name),f,captured)) ->
            let capturedString =
                Map.toSeq captured
                |> Seq.map (fun (Var(name),type_) -> sprintf "%s => %A" name type_)
                |> String.concat " "
            sprintf "closure rec <%s: %A> %A {%s} = %A" name f.type_ f.value.argument capturedString f.value.body
        | TypeDecl(Var(name),decl) ->
            match decl with
            | TyAlias(other) -> sprintf "type %s = %A" name other
            | Record(fields) -> 
                let fieldsString = 
                    Map.toSeq fields
                    |> Seq.map (fun (Var(name),type_) -> sprintf "%s: %A" name type_)
                    |> String.concat "; "
                sprintf "{ %s }" fieldsString

type Environment = { typeEnv: TypeEnv; typeNameEnv: Map<Var,Type>; recordEnv: Map<Var,RecordType> }
with
    member this.updateTypeEnv typeEnv =
        { typeEnv = typeEnv; typeNameEnv = this.typeNameEnv; recordEnv = this.recordEnv }
    member this.updateTypeNameEnv typeNameEnv =
        { typeEnv = this.typeEnv; typeNameEnv = typeNameEnv; recordEnv = this.recordEnv }
    member this.updateRecordEnv recordEnv =
        { typeEnv = this.typeEnv; typeNameEnv = this.typeNameEnv; recordEnv = recordEnv }
    member this.Apply subst =
        this.updateTypeEnv (this.typeEnv.Apply subst)

open State

let generalizeM (type_: Type): State<Environment,Scheme> = yaruzo{
    let! env = get
    return generalize env.typeEnv type_
}

let rec inferExpr' (expr: Closure.Expr): State.State<Environment,Substitution * TypedExpr> =
    let apply subst = modify (fun (env: Environment) -> env.Apply subst)
    let add name value = modify (fun (env: Environment) -> env.updateTypeEnv (env.typeEnv.Add name value))
    yaruzo{
        match expr with
        | Closure.Literal(x) -> return emptySubstitution,Literal(x).WithType intType
        | Closure.ExternRef(name) ->
            let! env = get
            let (TypeEnv(env)) = env.typeEnv
            match env.TryFind name with
            | None ->
                printfn "%A not found in the environment: %A" name env
                return emptySubstitution,(ExternRef(name)).WithType (newTyVar "t")
            | Some(scheme) ->
                return emptySubstitution,(ExternRef(name)).WithType (instantiate scheme)
        | Closure.Apply(f,xs) ->
            let! sf,f = inferExpr' f
            do! apply sf
            let! sx,xs = xs
                         |> List.map (fun x -> inferExpr' x)
                         |> forM
                         |> fmap List.unzip
            let subst = composeSubstitutionMany sx
            do! apply subst
            let t = newTyVar "t"
            let subst' = 
                let funType =
                    let xsType = xs |> List.map (fun x -> x.type_)
                    List.foldBack (fun (xType: Type) funType -> TArrow(xType.Apply subst,funType)) xsType (t.Apply subst)
                unify (f.type_.Apply subst) funType
            let subst = composeSubstitution subst subst'
            return subst,Apply(f.Apply subst,xs |> List.map (fun x -> x.Apply subst)).WithType (t.Apply subst)
        | Closure.If(cond,ifTrue,ifFalse) ->
            let! sc,cond = inferExpr' cond
            do! apply sc
            let! st,ifTrue = inferExpr' ifTrue
            do! apply st
            let! sf,ifFalse = inferExpr' ifFalse
            let subst = composeSubstitutionMany [sc; st; sf]
            let suni = unify (ifTrue.type_.Apply subst) (ifFalse.type_.Apply subst)
            let subst = composeSubstitution subst suni
            return subst,If(cond.Apply subst,ifTrue.Apply subst,ifFalse.Apply subst).WithType (ifTrue.type_.Apply subst)
        | Closure.BinOp(lhs,op,rhs) ->
            let! env = get
            let opType = 
                let op = Var(sprintf "%A" op)
                let (TypeEnv(env)) = env.typeEnv
                match env.TryFind op with
                | None -> failwithf "operator %A not found" op
                | Some(decl) -> instantiate decl
            let! slhs,lhs = inferExpr' lhs
            do! apply slhs
            let! srhs,rhs = inferExpr' rhs
            do! apply srhs
            let subst = composeSubstitution slhs srhs
            let retType = newTyVar "t"
            let suni = unify opType (TArrow(lhs.type_.Apply subst,TArrow(rhs.type_.Apply subst,retType)))
            let subst = composeSubstitution subst suni
            return subst,BinOp(lhs.Apply subst,op,rhs.Apply subst).WithType (retType.Apply subst)
        | Closure.Alias(name,value,body) ->
            let! sv,value = inferExpr' value
            do! apply sv
            let! env = get
            do! generalizeM value.type_ >>= add name 
            let! sb,body = inferExpr' body
            do! apply sb
            let subst = composeSubstitution sv sb
            return subst,Alias(name,value,body).WithType body.type_
        | Closure.AliasRec(name,value,body) ->
            let valueType = newTyVar "t"
            do! add name (Scheme.fromType valueType)
            let! sv,value = inferExpr' value
            do! apply sv
            let! env = get
            do! generalizeM value.type_ >>= add name
            let! sb,body = inferExpr' body
            return composeSubstitution sv sb,AliasRec(name,value.Apply sb,body).WithType body.type_
        | Closure.ApplyClosure(cls,applications) ->
            let folder (subst,applications) (name,expr) = yaruzo{
                let! s,expr = inferExpr' expr
                do! apply s
                return composeSubstitution subst s,Map.add name expr applications
            }
            let! subst,applications = foldM folder (emptySubstitution,Map.empty) (Map.toList applications)
            do! apply subst
            let! sc,cls = inferExpr' cls
            do! apply sc
            let subst = composeSubstitution subst sc
            let underlyingType = newTyVar "t"
            let suni = unify (cls.type_.Apply subst) (TClosure(underlyingType,applications |> Map.map (fun _ expr -> expr.type_.Apply subst)))
            let subst = composeSubstitution subst suni

            // the type of closure application is the underlying type of the closure
            return subst,ApplyClosure(cls.Apply subst,applications |> Map.map (fun _ t -> t.Apply subst) ).WithType (underlyingType.Apply subst)
        | Closure.RecordLiteral(fields) ->
            let! env = get
            let recordType types =
                let rec impl type_ types =
                    match types with
                    | [] -> Right(type_)
                    | type_' :: types when type_ = type_' -> impl type_ types
                    | type_' :: _ -> Left(type_,type_')
                match types with
                | [] -> failwith "record literal cannot be empty"
                | type_ :: [] -> type_
                | type_ :: types -> 
                    match impl type_ types with
                    | Right(type_) -> type_
                    | Left(type_,type_') -> failwithf "assumed record types %A and %A are different" type_ type_'
            let assumedTypes = fields
                               |> Map.toSeq
                               |> Seq.map fst
                               |> Seq.map 
                                    (
                                        fun field -> match env.recordEnv.TryFind field with
                                                     | None -> failwith "record type not found"
                                                     | Some(x) -> x
                                    )
                               |> Seq.toList
            let recordType = recordType assumedTypes

            let folder (subst,fields) (name,init) = yaruzo{
                do! apply subst
                let! s,init = inferExpr' init
                let subst = composeSubstitution subst s
                return subst,Map.add name init fields
            }
            let! subst,fields = foldM folder (emptySubstitution,Map.empty) (Map.toList fields)
            return subst,RecordLiteral(fields).WithType (TRecord(recordType))
        | Closure.RecordAccess(obj,name) -> 
            let! sobj,obj = inferExpr' obj
            match obj.type_ with
            | TRecord(RecordType(recordType)) ->
                match recordType.TryFind name with
                | Some(fieldType) -> return sobj,RecordAccess(obj,name).WithType (fieldType.Apply sobj)
                | None -> return failwithf "type %A does not have a field '%A'" recordType name 
            | _ -> return failwithf "not a record: %A" obj
    }

let rec inferExpr (env: Environment) (expr: Closure.Expr): Substitution * TypedExpr =
    let typeEnv = env.typeEnv
    match expr with
    | Closure.Literal(x) -> emptySubstitution,Literal(x).WithType intType
    | Closure.ExternRef(name) -> 
        let expr = ExternRef(name)
        let (TypeEnv(env)) = typeEnv
        match env.TryFind name with
        | None ->
            printfn "%A not found in the environment: %A" name env
            emptySubstitution,expr.WithType (newTyVar "t")
        | Some(scheme) ->
            emptySubstitution,expr.WithType (instantiate scheme)
    | Closure.Apply(f,xs) ->
        let sf,f = inferExpr env f
        let sx,xs = 
            xs
            |> List.map (fun x -> inferExpr (env.Apply sf) x)
            |> List.unzip
        let subst = composeSubstitutionMany (sf :: sx)
        let t = newTyVar "t"
        let subst' = 
            let funType = 
                let xsType = xs
                             |> List.map (fun x -> x.type_)
                List.foldBack (fun (xType: Type) funType -> TArrow(xType.Apply subst,funType)) xsType (t.Apply subst)
            unify (f.type_.Apply subst) funType
        let subst = composeSubstitution subst subst'
        subst,Apply(f.Apply subst,xs |> List.map (fun x -> x.Apply subst)).WithType (t.Apply subst)
    | Closure.If(cond,ifTrue,ifFalse) ->
        let sc,cond = inferExpr env cond
        let sc2 = unify cond.type_ boolType
        let subst = composeSubstitution sc sc2
        let st,ifTrue = inferExpr (env.Apply subst) ifTrue
        let subst = composeSubstitution subst st
        let sf,ifFalse = inferExpr(env.Apply subst) ifFalse
        let subst = composeSubstitution subst sf
        let sub = unify (ifTrue.type_.Apply subst) (ifFalse.type_.Apply subst)
        let subst = composeSubstitution subst sub
        let cond = cond.Apply subst
        let ifTrue = ifTrue.Apply subst
        let ifFalse = ifFalse.Apply subst
        subst,If(cond,ifTrue,ifFalse).WithType (ifTrue.type_.Apply subst)
    | Closure.BinOp(lhs,op,rhs) ->
        let opType =
            let op = Var(sprintf "%A" op)
            let (TypeEnv(env)) = typeEnv
            match Map.tryFind op env with
            | None -> failwithf "operator %A not found" op
            | Some(decl) -> instantiate decl
        let slhs,lhs = inferExpr env lhs
        let srhs,rhs = inferExpr (env.Apply slhs) rhs
        let subst = composeSubstitution slhs srhs
        let retType = newTyVar "t"
        let sop = unify opType (TArrow(lhs.type_.Apply subst,TArrow(rhs.type_.Apply subst,retType)))
        let subst = composeSubstitution subst sop
        subst,BinOp(lhs.Apply subst,op,rhs.Apply subst).WithType (retType.Apply subst)
    | Closure.Alias(name,value,body) ->
        let sv,value = inferExpr env value
        let typeEnv = (typeEnv.Apply sv).Add name (generalize (typeEnv.Apply sv) value.type_)
        let sb,body = inferExpr (env.updateTypeEnv typeEnv) body
        let subst = composeSubstitution sv sb
        subst,Alias(name,value.Apply subst,body.Apply subst).WithType (body.type_.Apply subst)
    | Closure.AliasRec(name,value,body) ->
        let valueType = newTyVar "t"
        let typeEnv = typeEnv.Add name (Scheme.fromType valueType)
        let sv,value = inferExpr (env.updateTypeEnv typeEnv) value
        let typeEnv = (typeEnv.Apply sv).Add name (generalize (typeEnv.Apply sv) value.type_)
        let sb,body = inferExpr (env.updateTypeEnv typeEnv) body
        let subst = composeSubstitution sv sb
        subst,AliasRec(name,value.Apply subst,body.Apply subst).WithType (body.type_.Apply subst)
    | Closure.ApplyClosure(cls,applications) ->
        let folder (subst,applications) name expr =
            let s,expr = inferExpr (env.Apply subst) expr
            composeSubstitution subst s,Map.add name expr applications
        let subst,applications = Map.fold folder (emptySubstitution,Map.empty) applications
        let typeEnv = typeEnv.Apply subst
        let sc,cls = inferExpr (env.updateTypeEnv typeEnv) cls
        let subst = composeSubstitution subst sc
        let su = unify cls.type_ (TClosure(newTyVar "t",applications |> Map.map (fun _ expr -> expr.type_.Apply subst)))
        let subst = composeSubstitution subst su

        // the type of closure application is the underlying type of the closure
        let type_ = match cls.type_.Apply subst with
                    | TClosure(type_,_) -> type_
                    | _ -> failwith "must be closure"
        subst,ApplyClosure(cls.Apply subst,applications).WithType type_
    | Closure.RecordLiteral(fields) ->
        let recordType types =
            let rec impl type_ types =
                match types with
                | [] -> Right(type_)
                | type_' :: types when type_ = type_' -> impl type_ types
                | type_' :: _ -> Left(type_,type_')
            match types with
            | [] -> failwith "record literal cannot be empty"
            | type_ :: [] -> type_
            | type_ :: types -> 
                match impl type_ types with
                | Right(type_) -> type_
                | Left(type_,type_') -> failwithf "assumed record types %A and %A are different" type_ type_'
        let assumedTypes = fields
                           |> Map.toSeq
                           |> Seq.map fst
                           |> Seq.map 
                                (
                                    fun field -> match env.recordEnv.TryFind field with
                                                 | None -> failwith "record type not found"
                                                 | Some(x) -> x
                                )
                           |> Seq.toList
        let recordType = recordType assumedTypes

        let folder (subst,fields) name init =
            let s,init = inferExpr (env.Apply subst) init
            let subst = composeSubstitution subst s
            subst,Map.add name init fields
        let subst,fields = Map.fold folder (emptySubstitution,Map.empty) fields
        subst,RecordLiteral(fields).WithType (TRecord(recordType))
    | Closure.RecordAccess(obj,name) -> 
        let sobj,obj = inferExpr env obj
        match obj.type_ with
        | TRecord(RecordType(recordType)) ->
            match recordType.TryFind name with
            | Some(fieldType) -> sobj,RecordAccess(obj,name).WithType (fieldType.Apply sobj)
            | None -> failwithf "type %A does not have a field '%A'" recordType name 
        | _ -> failwithf "not a record: %A" obj

let rec resolveType (env: Environment) (signature: Signature): Type =
    match signature with
    | SigLiteral(name) -> 
        match env.typeNameEnv.TryFind name with
        | None -> failwithf "type %A not found in env %A" name env.typeNameEnv
        | Some(type_) -> type_
    | SigArrow(lhs,rhs) ->
        let lhs = resolveType env lhs
        let rhs = resolveType env rhs
        TArrow(lhs,rhs)

let inferDecl' (decl: Closure.Declaration): State<Environment,Substitution * Declaration option> = yaruzo{
    let apply subst = modify (fun (env: Environment) -> env.Apply subst)
    let addTypeEnv name value = modify (fun (env: Environment) -> env.updateTypeEnv (env.typeEnv.Add name value))
    let addAliasEnv name type_ = modify (fun (env: Environment) -> env.updateTypeNameEnv (env.typeNameEnv.Add (name,type_)))
    let addRecordEnv name record = modify (fun (env: Environment) -> env.updateRecordEnv (env.recordEnv.Add (name,record)))
    match decl with
    | Closure.FreeValue(name,value) ->
        let! s,value = inferExpr' value
        do! apply s
        let! env = get
        let! schemed = 
            generalizeM value.type_
            >>= fun scheme -> yaruzo{ return { SchemedExpr.value = value.value; type_ = scheme } }
        do! addTypeEnv name schemed.type_
        return s,Some(FreeValue(name,schemed))
    | Closure.FreeFunction(name,f) ->
        let argTypes = List.map (fun _ -> newTyVar "t") f.argument
        let! env = get
        let s,body = 
            let innerEnv = List.zip f.argument argTypes
                           |> Map.ofList
                           |> Map.map (fun _ t -> Scheme.fromType t)
                           |> TypeEnv
                           |> env.typeEnv.Merge
            eval (env.updateTypeEnv innerEnv) (inferExpr' f.body)
        do! apply s
        let! thisScheme = 
            let thisType = List.foldBack (fun argType thisType -> TArrow(argType,thisType)) argTypes body.type_
                           |> fun type_ -> type_.Apply s
            generalizeM thisType
        do! addTypeEnv name thisScheme
        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme}
        return s,Some(FreeFunction(name,value))
    | Closure.FreeRecFunction(name,f) ->
        let thisType = newTyVar "t"
        let argTypes = List.map (fun _ -> newTyVar "t") f.argument
        let! env = get
        let s1,body = 
            let innerEnv =
                let env = List.zip f.argument argTypes
                          |> Map.ofList
                          |> Map.map (fun _ t -> Scheme.fromType t)
                          |> TypeEnv
                          |> env.typeEnv.Merge
                env.Add name (Scheme.fromType thisType)
            eval (env.updateTypeEnv innerEnv) (inferExpr' f.body)
        do! apply s1
        let s2 = 
            let thisType' = List.foldBack (fun argType thisType -> TArrow(argType,thisType)) argTypes body.type_
                            |> fun type_ -> type_.Apply s1
            unify (thisType.Apply s1) thisType'
        let s = composeSubstitution s1 s2
        do! apply s
        let! thisScheme = generalizeM (thisType.Apply s)
        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme}  
        return s,Some(FreeRecFunction(name,value))
    | Closure.ClosureDecl(Closure.Closure(name,f,capturedVariables)) ->
        let argTypes = List.map (fun _ -> newTyVar "t") f.argument
        let captured = capturedVariables
                       |> Set.map (fun v -> v,newTyVar "t")
                       |> Map.ofSeq
        let! env = get
        let s,body = 
            let innerEnv = 
                let capturedEnv = Map.map (fun _ t -> Scheme.fromType t) captured
                                  |> TypeEnv
                let env = env.typeEnv.Merge capturedEnv
                List.zip f.argument argTypes
                |> Map.ofList
                |> Map.map (fun _ t -> Scheme.fromType t)
                |> TypeEnv
                |> env.Merge
            eval (env.updateTypeEnv innerEnv) (inferExpr' f.body)
        do! apply s
        let captured = captured
                       |> Map.map (fun _ t -> t.Apply s)
        let! thisScheme = 
            let thisType = List.foldBack (fun argType thisType -> TArrow(argType,thisType)) argTypes body.type_
                           |> fun type_ -> type_.Apply s
            let closureType = TClosure(thisType.Apply s,captured)
            generalizeM closureType

        do! addTypeEnv name thisScheme

        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme}
        return s,Some(ClosureDecl(Closure(name,value,captured)))
    | Closure.ClosureRecDecl(Closure.Closure(name,f,capturedVariables)) ->
        let thisType = newTyVar "t"
        let argTypes = List.map (fun _ -> newTyVar "t") f.argument
        let captured = capturedVariables
                       |> Set.map (fun v -> v,newTyVar "t")
                       |> Map.ofSeq
        
        let! env = get
        
        let s1,body = 
            let innerEnv = 
                let env = List.zip f.argument argTypes
                          |> Map.ofList
                          |> Map.map (fun _ t -> Scheme.fromType t)
                          |> TypeEnv
                          |> env.typeEnv.Merge
                let env = env.Add name (Scheme.fromType thisType)
                let capturedEnv = Map.map (fun _ t -> Scheme.fromType t) captured
                                  |> TypeEnv
                env.Merge capturedEnv
            eval (env.updateTypeEnv innerEnv) (inferExpr' f.body)

        do! apply s1

        printfn "s1 %A" s1

        let captured = captured
                       |> Map.map (fun _ t -> t.Apply s1)
        let closureType =
            let thisType = List.foldBack (fun argType thisType -> TArrow(argType,thisType)) argTypes body.type_
                           |> fun type_ -> type_.Apply s1
            TClosure(thisType.Apply s1,captured)
        let s2 = unify thisType closureType
        let s = composeSubstitution s1 s2

        printfn "s2 %A" s2

        do! apply s

        let! env = get
        let! thisScheme = generalizeM (thisType.Apply s)

        do! addTypeEnv name thisScheme

        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme.Apply s}
        return s,Some(ClosureRecDecl(Closure(name,value,captured)))
    | Closure.TypeDecl(name,decl) -> 
        match decl with
        | Closure.Record(fields) -> 
            let! env = get
            let recordType = fields
                             |> Map.map (fun _ signature -> resolveType env signature)
                             |> RecordType                               
            do! fields
                |> Map.toList
                |> List.map fst
                |> forEachM (fun name -> addRecordEnv name recordType)
            do! addAliasEnv name (TRecord(recordType))
            
            return emptySubstitution,None
        | Closure.TyAlias(signature) -> 
            let! env = get
            do! addAliasEnv name (resolveType env signature)
            return emptySubstitution,None
}

let inferDecl (env: Environment) (decl: Closure.Declaration): Substitution * Either<Map<Var,Type> * Map<Var,RecordType>,Declaration> =
    match decl with
    | Closure.FreeValue(name,value) ->
        let s,value = inferExpr env value
        let env = env.Apply s
        let (schemed: SchemedExpr) = {value = value.value; type_ = generalize env.typeEnv value.type_} 
        s,Right(FreeValue(name,schemed))
    | Closure.FreeFunction(name,f) ->
        let argTypes = List.map (fun _ -> newTyVar "t") f.argument
        let innerEnv = List.zip f.argument argTypes
                       |> Map.ofList
                       |> Map.map (fun _ t -> Scheme.fromType t)
                       |> TypeEnv
                       |> env.typeEnv.Merge
        let s,body = inferExpr (env.updateTypeEnv innerEnv) f.body
        let thisScheme = 
            let thisType = List.foldBack (fun argType thisType -> TArrow(argType,thisType)) argTypes body.type_
                           |> fun type_ -> type_.Apply s
            generalize (env.typeEnv.Apply s) thisType
        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme}
        s,Right(FreeFunction(name,value))
    | Closure.FreeRecFunction(name,f) ->
        let thisType = newTyVar "t"
        let argTypes = List.map (fun _ -> newTyVar "t") f.argument
        let innerEnv =
            let env = List.zip f.argument argTypes
                      |> Map.ofList
                      |> Map.map (fun _ t -> Scheme.fromType t)
                      |> TypeEnv
                      |> env.typeEnv.Merge
            env.Add name (Scheme.fromType thisType)
        let s1,body = inferExpr (env.updateTypeEnv innerEnv) f.body
        let s2 = 
            let thisType' = List.foldBack (fun argType thisType -> TArrow(argType,thisType)) argTypes body.type_
                            |> fun type_ -> type_.Apply s1
            unify (thisType.Apply s1) thisType'
        let s = composeSubstitution s1 s2
        let thisScheme = generalize (env.typeEnv.Apply s) (thisType.Apply s)
        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme}  
        s,Right(FreeRecFunction(name,value))
    | Closure.ClosureDecl(Closure.Closure(name,f,capturedVariables)) ->
        let argTypes = List.map (fun _ -> newTyVar "t") f.argument
        let captured = capturedVariables
                       |> Set.map (fun v -> v,newTyVar "t")
                       |> Map.ofSeq
        let capturedEnv = Map.map (fun _ t -> Scheme.fromType t) captured
                          |> TypeEnv
        let innerEnv = 
            let env = env.typeEnv.Merge capturedEnv
            List.zip f.argument argTypes
            |> Map.ofList
            |> Map.map (fun _ t -> Scheme.fromType t)
            |> TypeEnv
            |> env.Merge
        let s,body = inferExpr (env.updateTypeEnv innerEnv) f.body
        let captured = captured
                       |> Map.map (fun _ t -> t.Apply s)
        let thisScheme = 
            let thisType = List.foldBack (fun argType thisType -> TArrow(argType,thisType)) argTypes body.type_
                           |> fun type_ -> type_.Apply s
            let closureType = TClosure(thisType.Apply s,captured)
            generalize (env.typeEnv.Apply s) closureType
        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme}
        s,Right(ClosureDecl(Closure(name,value,captured)))
    | Closure.ClosureRecDecl(Closure.Closure(name,f,capturedVariables)) ->
        let thisType = newTyVar "t"
        let argTypes = List.map (fun _ -> newTyVar "t") f.argument
        let captured = capturedVariables
                       |> Set.map (fun v -> v,newTyVar "t")
                       |> Map.ofSeq
        let innerEnv = 
            let env = List.zip f.argument argTypes
                      |> Map.ofList
                      |> Map.map (fun _ t -> Scheme.fromType t)
                      |> TypeEnv
                      |> env.typeEnv.Merge
            let env = env.Add name (Scheme.fromType thisType)
            let capturedEnv = Map.map (fun _ t -> Scheme.fromType t) captured
                              |> TypeEnv
            env.Merge capturedEnv
        let s1,body = inferExpr (env.updateTypeEnv innerEnv) f.body
        printfn "s1 %A" s1
        let captured = captured
                       |> Map.map (fun _ t -> t.Apply s1)
        let closureType =
            let thisType = List.foldBack (fun argType thisType -> TArrow(argType,thisType)) argTypes body.type_
                           |> fun type_ -> type_.Apply s1
            TClosure(thisType.Apply s1,captured)
        let s2 = unify thisType closureType
        printfn "s2 %A" s2
        let s = composeSubstitution s1 s2
        let thisScheme = generalize (env.typeEnv.Apply s) (thisType.Apply s)
        let value = {value = {argument = f.argument; body = body.Apply s}; type_ = thisScheme}
        s,Right(ClosureRecDecl(Closure(name,value,captured)))
    | Closure.TypeDecl(name,decl) -> 
        match decl with
        | Closure.Record(fields) -> 
            let recordType = fields
                             |> Map.map (fun _ signature -> resolveType env signature)
                             |> RecordType
            let recordEnv = fields
                            |> Map.toSeq
                            |> Seq.map fst
                            |> Seq.fold (fun env name -> Map.add name recordType env) env.recordEnv
            emptySubstitution,Left(Map.add name (TRecord(recordType)) env.typeNameEnv,recordEnv)
        | Closure.TyAlias(signature) -> 
            let type_ = resolveType env signature
            emptySubstitution,Left(Map.add name type_ env.typeNameEnv,env.recordEnv)

let inferDecls' (env: Environment) (decls: Closure.Declaration list): Declaration list =
    let apply subst = modify (fun (env: Environment) -> env.Apply subst)
    let folder decls decl = yaruzo{
        let! s,declaration = inferDecl' decl
        do! apply s
        match declaration with
        | None -> return decls
        | Some(decl) -> return decl :: decls
    }
    let decls = foldM folder [] decls
                |> eval env
    // keep the ordering of declarations
    List.rev decls

let inferDecls (env: Environment) (decls: Closure.Declaration list): Declaration list =
    let folder (env,decls) decl =
        let s,declaration = inferDecl env decl
        let env = env.Apply s
        match declaration with
        | Left(typeNameEnv,recordEnv) -> (env.updateTypeNameEnv typeNameEnv).updateRecordEnv recordEnv,decls
        | Right(decl) -> env.updateTypeEnv(env.typeEnv.Add decl.Name decl.Scheme),decl :: decls
    let _,decls = List.fold folder (env,[]) decls
    // keep the ordering of declarations
    List.rev decls