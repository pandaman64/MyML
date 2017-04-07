module EarlyTypeInference

open Common
open Common.State

module TypeSystem =
    [<StructuredFormatDisplayAttribute("{AsString}")>]
    type TVar = TVar of Var
    with
        member this.AsString =
            let (TVar(Var(name))) = this
            sprintf "'%s" name

    type Substitution = Map<TVar,Type>
    and TRec = TRec of Map<Var,Type>
    and 
        [<StructuredFormatDisplayAttribute("{AsString}")>]
        Type =   TVariable of TVar
               | TConstructor of Var
               | TArrow of Type * Type
               | TRecord of TRec
    with
        member this.Apply (s: Substitution) = 
            match this with
            | TVariable(v) -> 
                match s.TryFind v with
                | Some(t) -> t
                | None -> this
            | TConstructor(_) -> this
            | TArrow(f,x) -> 
                TArrow(f.Apply s,x.Apply s)
            | TRecord(TRec(record)) -> 
                record
                |> Map.map (fun _ t -> t.Apply s)
                |> TRec
                |> TRecord
        member this.freeTypeVariables = 
            match this with
            | TVariable(v) -> Set.singleton v
            | TConstructor(_) -> Set.empty
            | TArrow(f,x) -> Set.union f.freeTypeVariables x.freeTypeVariables
            | TRecord(TRec(record)) -> 
                record
                |> Map.toSeq
                |> Seq.map snd
                |> Seq.map (fun t -> t.freeTypeVariables)
                |> Set.unionMany
        member this.AsString =
            match this with
            | TVariable(v) -> sprintf "%A" v
            | TConstructor(Var(name)) -> sprintf "%s" name
            | TArrow(f,x) -> sprintf "(%A -> %A)" f x
            | TRecord(TRec(record)) ->
                record
                |> Map.fold (fun s (Var(field)) type_ -> String.concat " " [ s; sprintf "%A: %A" field type_ ]) ""
                |> fun s -> sprintf "{ %s }" s

    [<StructuredFormatDisplayAttribute("{AsString}")>]
    type Scheme = 
        { bindings: Set<TVar>; type_: Type }
    with
        member this.Apply s =
            let s = this.bindings 
                    |> Set.fold (fun s v -> Map.remove v s) s
            { bindings = this.bindings; type_ = this.type_.Apply s }
        member this.freeTypeVariables =
            this.type_.freeTypeVariables - this.bindings
        member this.AsString =
            let bindingsString = Set.fold (fun s v -> sprintf "%sFA.%A" s v) "" this.bindings
            sprintf "%s%A" bindingsString this.type_

    let intType = TConstructor(Var("Int"))
    let boolType = TConstructor(Var("Bool"))

    type Variables = Variables of Map<Var,Scheme>
    with
        member this.Apply s =
            let (Variables(variables)) = this
            variables
            |> Map.map (fun _ scheme -> scheme.Apply s)
            |> Variables
        member this.freeTypeVariables =
            let (Variables(variables)) = this
            variables
            |> Map.toSeq
            |> Seq.map snd
            |> Seq.map (fun scheme -> scheme.freeTypeVariables)
            |> Set.unionMany
        member this.Add name scheme =
            let (Variables(variables)) = this
            Map.add name scheme variables
            |> Variables
        member this.TryFind name =
            let (Variables(variables)) = this
            variables.TryFind name

    type Environment = 
        { variables: Variables; recordFields: Map<Var,TRec>; typeAliases: Map<Var,Type> }
    with
        member this.Apply s =
            {
                variables = this.variables.Apply s;
                recordFields = this.recordFields;
                typeAliases = this.typeAliases;
            }
        member this.freeTypeVariables =
            this.variables.freeTypeVariables

    let emptySubst: Substitution = Map.empty
    let composeSubst (s1: Substitution) (s2: Substitution) : Substitution = 
        let s1 = s1 |> Map.map (fun _ t -> t.Apply s2)
        s2 
        |> Map.fold (fun s1 v t -> Map.add v t s1) s1
    let (<+) s1 s2 = composeSubst s1 s2
    let composeSubstMany (xs: Substitution seq) : Substitution =
        Seq.fold (fun s s' -> s <+ s') emptySubst xs

    let rec unify (t1: Type) (t2: Type) : Substitution =
        let occurCheck (v: TVar) (t: Type) : bool =
            t.freeTypeVariables.Contains v
        let bind (v: TVar) (t: Type) = 
            match t with
            | TVariable(v') when v = v' -> emptySubst
            | t when occurCheck v t -> failwithf "Occur check failed %A -> %A" v t
            | _ -> Map.add v t emptySubst
        match t1,t2 with
        | TConstructor(c1),TConstructor(c2) when c1 = c2 -> emptySubst
        | TArrow(f1,x1),TArrow(f2,x2) -> 
            let sf = unify f1 f2
            let sx = unify (x1.Apply sf) (x2.Apply sf)
            sf <+ sx
        | TVariable(v),t -> bind v t
        | t,TVariable(v) -> bind v t
        | TRecord(TRec(fields1)),TRecord(TRec(fields2)) ->
            let folder s name (t2: Type) =
                match fields1.TryFind name with
                | None -> failwithf "field %A not found in %A" name fields1
                | Some(t1) -> s <+ unify (t1.Apply s) (t2.Apply s)
            Map.fold folder emptySubst fields2
        | _ -> failwithf "Type mismatch %A and %A" t1 t2
    let unifyM (t1: Type) (t2: Type) : State<Environment,Substitution> =
        let subst = unify t1 t2
        yaruzo{
            do! get >>= fun e -> set (e.Apply subst)
            return subst
        }

    let newTyVar =
        let mutable counter = 0
        let f name =
            counter <- counter + 1
            TVariable(TVar(Var(sprintf "%s@%d" name counter)))
        f

    let instantiate (scheme: Scheme) : Type =
        let subst = Set.fold (fun s v -> Map.add v (newTyVar "a") s) emptySubst scheme.bindings
        scheme.type_.Apply subst

    let generalize (env: Environment) (type_: Type) : Scheme =
        let bindings = type_.freeTypeVariables - env.freeTypeVariables
        { bindings = bindings; type_ = type_ }

    let generalizeM (type_: Type) : State<Environment,Scheme> =
        get |> fmap (fun e -> generalize e type_)

open TypeSystem

module Inner =
    [<StructuredFormatDisplayAttribute("{AsString}")>]
    type PlainExpr =  
          Literal of int
        | Apply of Expr * Expr list
        | BinOp of Expr * Operator * Expr
        | VarRef of Var
        | If of Expr * Expr * Expr
        | RecordLiteral of Map<Var,Expr>
        | RecordAccess of Expr * Var
        | Fun of Var list * Expr
        | Let of Var * Expr * Expr
        | LetRec of Var * Expr * Expr
    with
        member this.AsString =
            match this with
            | Literal(x) -> sprintf "%d" x
            | Apply(f,xs) -> sprintf "(%A %A)" f xs
            | BinOp(lhs,op,rhs) -> sprintf "(%A %A %A)" lhs op rhs
            | VarRef(Var(v)) -> sprintf "%A" v
            | If(cond,ifTrue,ifFalse) -> sprintf "if %A then %A else %A" cond ifTrue ifFalse
            | RecordLiteral(fields) ->
                Map.fold (fun s (Var(field)) value -> sprintf "%s %s %A" s field value) "" fields
                |> fun s -> sprintf "{ %s }" s
            | RecordAccess(obj,Var(field)) -> sprintf "%A.%s" obj field
            | Fun(arguments,value) ->
                let arguments = arguments |> List.map (fun (Var(name)) -> sprintf "%s" name) |> String.concat " "
                sprintf "fun %s = %A" arguments value
            | Let(Var(name),value,body) -> sprintf "let %s = %A in %A" name value body
            | LetRec(Var(name),value,body) -> sprintf "let rec %s = %A in %A" name value body

    and
        [<StructuredFormatDisplayAttribute("{AsString}")>]
        Expr = { value: PlainExpr; type_: Type ref }
    with
        member this.Apply s : unit =
            match this.value with
            | Literal(_)
            | VarRef(_) -> ()
            | Apply(f,xs) -> 
                f.Apply s
                xs |> List.fold (fun () x -> x.Apply s) ()
            | BinOp(lhs,_,rhs) ->
                lhs.Apply s
                rhs.Apply s
            | If(cond,ifTrue,ifFalse) -> 
                cond.Apply s
                ifTrue.Apply s
                ifFalse.Apply s
            | RecordLiteral(fields) ->
                fields
                |> Map.fold (fun () _ e -> e.Apply s) ()
            | RecordAccess(obj,_) -> obj.Apply s
            | Fun(_,value) -> value.Apply s
            | Let(_,value,body)
            | LetRec(_,value,body) -> 
                value.Apply s
                body.Apply s
            this.type_ := (!this.type_).Apply s
        member this.freeTypeVariables = (!this.type_).freeTypeVariables
        member this.AsString =
            sprintf "<%A: %A>" this.value !this.type_

    let addVariable name scheme = yaruzo{
        let! e = get
        do! set { 
            variables = e.variables.Add name scheme;
            recordFields = e.recordFields;
            typeAliases = e.typeAliases
        }
    }
    let apply s : State<Environment,unit> = yaruzo{
        do! get >>= (fun e -> set (e.Apply s))
    }

    [<StructuredFormatDisplayAttribute("{AsString}")>]
    type PlainDeclaration =   LetDecl of Var * Expr
                            | LetRecDecl of Var * Expr
    with
        member this.AsString = 
            match this with
            | LetDecl(Var(name),value) -> sprintf "let %s = %A" name value
            | LetRecDecl(Var(name),value) -> sprintf "let rec %s = %A" name value
    [<StructuredFormatDisplayAttribute("{AsString}")>]
    type Declaration = { value: PlainDeclaration; scheme: Scheme }
    with
        member this.Name = 
            match this.value with
            | LetDecl(name,_) 
            | LetRecDecl(name,_) -> name
        member this.AsString =
            sprintf "declaration %A %A" this.scheme this.value
    
    let rec inferExpr (expr: AlphaTransform.Expr) : State<Environment,Substitution * Expr> = 
        yaruzo{
            match expr with
            | AlphaTransform.Expr.Literal(x) -> return Map.empty,{ value = Literal(x); type_ = ref (intType) }
            | AlphaTransform.Expr.Apply(f,xs) -> 
                printfn "xs = %A" xs
                let! sf,f = inferExpr f
                let! sxs,xs = foldBackM (fun (s,xs) x -> yaruzo{
                                 let! s',x = inferExpr x
                                 return s <+ s',x :: xs
                              }) (emptySubst,[]) xs

                printfn "xs = %A" xs

                f.Apply sxs

                let retType = newTyVar "a"
                let fType = List.foldBack (fun x retType -> TArrow(!x.type_,retType)) xs retType
                let! suni = unifyM !f.type_ fType

                let subst = sf <+ sxs <+ suni
                f.Apply subst
                xs |> List.fold (fun () x -> x.Apply subst) ()

                return subst,{ value = Apply(f,xs); type_ = ref (retType.Apply subst) }
            | AlphaTransform.Expr.BinOp(lhs,op,rhs) ->
                let! slhs,lhs = inferExpr lhs
                let! srhs,rhs = inferExpr rhs

                let! opType = yaruzo{
                    let! variables = fmap (fun e -> e.variables) get 
                    match variables.TryFind (Var(op.AsString)) with
                    | None -> failwithf "operator %A not found in %A" op variables
                    | Some(scheme) -> return instantiate scheme
                }
                let retType = newTyVar "a"
                let! suni = unifyM (TArrow(!lhs.type_,TArrow(!rhs.type_,retType))) opType
                
                let subst = slhs <+ srhs <+ suni
                lhs.Apply subst
                rhs.Apply subst

                return subst,{ value = BinOp(lhs,op,rhs); type_ = ref (retType.Apply subst) }
            | AlphaTransform.Expr.VarRef(v) ->
                let! variables = fmap (fun e -> e.variables) get
                match variables.TryFind v with
                | None -> failwithf "variable %A not found in %A" v variables
                | Some(scheme) -> return emptySubst,{ value = VarRef(v); type_ = ref (instantiate scheme) }
            | AlphaTransform.Expr.If(cond,ifTrue,ifFalse) -> 
                let! sc,cond = inferExpr cond
                
                let! subst = unifyM !cond.type_ boolType

                let! sTrue,ifTrue = inferExpr ifTrue
                let! sFalse,ifFalse = inferExpr ifFalse
                
                let! subst' = unifyM !ifTrue.type_ !ifFalse.type_
                let subst = sc <+ sTrue <+ sFalse <+ subst <+ subst'

                cond.Apply subst
                ifTrue.Apply subst
                ifFalse.Apply subst

                return subst,{ value = If(cond,ifTrue,ifFalse); type_ = ifTrue.type_ }
            | AlphaTransform.Expr.RecordLiteral(fields) ->
                let! s,assumedType,fields = 
                    foldM (fun (s,assumption,fields) (name,value) -> yaruzo{
                        let! sv,value = inferExpr value
                        let! thisAssumption = get |> fmap (fun e -> e.recordFields.TryFind name)
                        let assumption = 
                            match thisAssumption with
                            | Some(_) when assumption = None -> thisAssumption
                            | Some(_) when assumption = thisAssumption -> assumption
                            | Some(_) -> failwithf "Record assumption mismatch %A vs %A" assumption thisAssumption
                            | None -> failwithf "Record field %A not found" name 
                        return s <+ sv,assumption,Map.add name value fields
                    }) (emptySubst,None,Map.empty) (Map.toList fields)
                match assumedType with
                | None -> failwith "Record type cannot be assumed"
                | Some(TRec(record)) -> 
                    let! s' = (Map.toList fields)
                              |> foldM 
                                (fun s (name,value) -> yaruzo{
                                    match record.TryFind name with
                                    | None -> failwithf "field %A not found in record %A" name record
                                    | Some(type_) -> 
                                        let! suni = unifyM type_ !value.type_
                                        return s <+ suni
                                }) emptySubst
                    let subst = s <+ s'
                    
                    fields |> Map.fold (fun () _ v -> v.Apply subst) ()

                    return subst,{ value = RecordLiteral(fields); type_ = ref (TRecord(TRec(record))) }
            | AlphaTransform.Expr.RecordAccess(obj,field) ->
                let! sobj,obj = inferExpr obj
                match !obj.type_ with
                | TRecord(TRec(record)) -> 
                    match record.TryFind field with
                    | None -> failwithf "field %A not found in %A" field record
                    | Some(type_) -> return sobj,{ value = RecordAccess(obj,field); type_ = ref type_ }
                | _ -> failwithf "%A is not a record" obj
            | AlphaTransform.Expr.Let(name,arguments,value,body) ->
                let arguments = List.map (fun arg -> arg,newTyVar "a") arguments
                let! sv,value,valueScheme = yatteiki $ yaruzo{
                    do! forEachM (fun (arg,type_) -> addVariable arg { bindings = Set.empty; type_ = type_ }) arguments
                    let! sv,value = inferExpr value
                    let value = 
                        if arguments.IsEmpty then value 
                        else    
                            let type_ = List.foldBack (fun (_,type_) funType -> TArrow(type_,funType)) arguments !value.type_
                            { value = Fun(arguments |> List.map fst,value); type_ = ref type_ }
                    let! valueScheme = generalizeM !value.type_
                    return sv,value,valueScheme
                }
                let! subst,whole = yatteiki $ yaruzo{
                    do! addVariable name valueScheme

                    let! sb,body = inferExpr body
                    let subst = sv <+ sb

                    value.Apply subst

                    return subst,{ value = Let(name,value,body); type_ = body.type_ }
                }
                return subst,whole
            | AlphaTransform.Expr.LetRec(name,arguments,value,body) ->
                let arguments = List.map (fun arg -> arg,newTyVar "a") arguments
                let thisType = newTyVar "a"
                let! sv,value = yatteiki $ yaruzo{
                    do! forEachM (fun (arg,type_) -> addVariable arg { bindings = Set.empty; type_ = type_ }) arguments
                    do! addVariable name { bindings = Set.empty; type_ = thisType }
                    let! sv,value = inferExpr value
                    return sv,value
                }
                
                let! suni = unifyM thisType !value.type_
                value.Apply suni

                let! subst,whole = yatteiki $ yaruzo{
                    let value = 
                        if arguments.IsEmpty then value 
                        else
                            let type_ = List.foldBack (fun (_,type_) funType -> TArrow(type_,funType)) arguments !value.type_
                            { value = Fun(arguments |> List.map fst,value); type_ = ref type_ }
                    
                    do! generalizeM !value.type_ >>= addVariable name 

                    let! sb,body = inferExpr body
                    let subst = sv <+ sb

                    value.Apply subst

                    return subst,{ value = Let(name,value,body); type_ = body.type_ }
                }
                return subst,whole
        }
    let inferDecl (decl: AlphaTransform.Declaration) : State<Environment,Option<Declaration>> = 
        let rec parseSignature signature = yaruzo{
            match signature with
            | SigLiteral(name) -> 
                let! e = get
                match e.typeAliases.TryFind name with
                | None -> failwithf "type %A not found in %A" name e.typeAliases
                | Some(type_) -> return type_
            | SigArrow(f,x) ->
                let! f = parseSignature f
                let! x = parseSignature x
                return TArrow(f,x)
            | SigTyVar(name) -> return TVariable(TVar(name))
        }
        yaruzo{
            match decl with
            | AlphaTransform.Declaration.TypeDecl(name,decl) ->
                match decl with
                | AlphaTransform.TyAlias(signature) -> 
                    let! type_ = parseSignature signature
                    let! e = get
                    do! set {
                        typeAliases = Map.add name type_ e.typeAliases;
                        variables = e.variables;
                        recordFields = e.recordFields
                    }
                    return None
                | AlphaTransform.Record(fields) ->
                    let! fields = 
                        Map.toList fields
                        |> mapM (fun (name,signature) -> parseSignature signature |> fmap (fun s -> name,s))
                        |> fmap (fun fields -> Map.ofList fields)

                    let recordType = TRec(fields)
                    let type_ = TRecord(recordType)

                    let! e = get
                    do! set {
                        typeAliases = Map.add name type_ e.typeAliases;
                        variables = e.variables;
                        recordFields = Map.fold (fun recordFields name _ -> Map.add name recordType recordFields) e.recordFields fields
                    }
                    return None
            | AlphaTransform.Declaration.LetDecl(name,arguments,value) -> 
                let arguments = arguments |> List.map (fun arg -> arg,newTyVar "a")
                let! sv,value = yatteiki $ yaruzo{
                    do! forEachM (fun (arg,type_) -> addVariable arg { bindings = Set.empty; type_ = type_ }) arguments
                    let! sv,value = inferExpr value
                    return sv,value
                }

                let value = 
                    match arguments with
                    | [] -> value
                    | _ -> 
                        let thisType = List.foldBack (fun (_,type_) retType -> TArrow(type_,retType)) arguments !value.type_
                        { value = Fun(arguments |> List.map fst,value); type_ = ref thisType }

                value.Apply sv
                let! scheme = generalizeM !value.type_

                return Some({ value = LetDecl(name,value); scheme = scheme })
            | AlphaTransform.Declaration.LetRecDecl(name,arguments,value) ->
                let arguments = arguments |> List.map (fun arg -> arg,newTyVar "a")
                let thisType = newTyVar "a"
                let! sv,value = yatteiki $ yaruzo{
                    do! forEachM (fun (arg,type_) -> addVariable arg { bindings = Set.empty; type_ = type_ }) arguments
                    do! addVariable name { bindings = Set.empty; type_ = thisType }
                    let! sv,value = inferExpr value
                    return sv,value
                }

                let value = 
                    match arguments with
                    | [] -> value
                    | _ -> 
                        let thisType = List.foldBack (fun (_,type_) retType -> TArrow(type_,retType)) arguments !value.type_
                        { value = Fun(arguments |> List.map fst,value); type_ = ref thisType }

                let! suni = unifyM thisType !value.type_

                value.Apply (sv <+ suni)

                let! scheme = generalizeM !value.type_

                return Some({ value = LetDecl(name,value); scheme = scheme })
        }

type Expr = Inner.Expr
type Declaration = Inner.Declaration

type Environment = TypeSystem.Environment

let inferDecls (env: Environment) (decls: AlphaTransform.Declaration list) : Declaration list =
    let decls = eval env $ yaruzo{
        let! decls = decls |> foldM (fun decls decl -> yaruzo {
                        let! decl = Inner.inferDecl decl
                        match decl with
                        | None -> return decls
                        | Some(decl) -> 
                            do! Inner.addVariable decl.Name decl.scheme
                            return decl :: decls
                     }) []
        return decls
    }
    List.rev decls