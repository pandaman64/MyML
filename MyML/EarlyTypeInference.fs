module EarlyTypeInference

open Common
open Common.State

module TypeSystem =
    type TVar = TVar of Var
    type Substitution = Map<TVar,Type>
    and Substitutable = interface
        abstract member Apply : Substitution -> Substitutable
        abstract member freeTypeVariables : Set<TVar>
    end
    and TRec = TRec of Map<Var,Type>
    and Type =   TVariable of TVar
               | TConstructor of Var
               | TArrow of Type * Type
               | TRecord of TRec
                   interface Substitutable with
                       member this.Apply (s: Substitution) = 
                           match this with
                           | TVariable(v) -> 
                               match s.TryFind v with
                               | Some(t) -> t :> Substitutable
                               | None -> this :> Substitutable
                           | TConstructor(_) -> this :> Substitutable
                           | TArrow(f,x) -> 
                                TArrow(downcast (f :> Substitutable).Apply s,downcast (x :> Substitutable).Apply s) :> Substitutable
                           | TRecord(TRec(record)) -> 
                               record
                               |> Map.map (fun _ t -> downcast (t :> Substitutable).Apply s)
                               |> TRec
                               |> TRecord
                               :> Substitutable
                       member this.freeTypeVariables = 
                           match this with
                           | TVariable(v) -> Set.singleton v
                           | TConstructor(_) -> Set.empty
                           | TArrow(f,x) -> Set.union (f :> Substitutable).freeTypeVariables (x :> Substitutable).freeTypeVariables
                           | TRecord(TRec(record)) -> 
                               record
                               |> Map.toSeq
                               |> Seq.map snd
                               |> Seq.map (fun t -> (t :> Substitutable).freeTypeVariables)
                               |> Set.unionMany

    type Scheme = 
        { bindings: Set<TVar>; type_: Type }
        interface Substitutable with
            member this.Apply s =
                let s = this.bindings 
                        |> Set.fold (fun s v -> Map.remove v s) s
                upcast { bindings = this.bindings; type_ = downcast (this.type_ :> Substitutable).Apply s }
            member this.freeTypeVariables =
                (this.type_ :> Substitutable).freeTypeVariables - this.bindings   

    type TypeVariableEnv = 
        TypeVariableEnv of Map<TVar,Scheme>
            interface Substitutable with
                member this.Apply s =
                    let (TypeVariableEnv(env)) = this
                    env
                    |> Map.map (fun _ scheme -> downcast (scheme :> Substitutable).Apply s)
                    |> TypeVariableEnv
                    :> Substitutable
                member this.freeTypeVariables =
                    let (TypeVariableEnv(env)) = this
                    env
                    |> Map.toSeq
                    |> Seq.map snd
                    |> Seq.map (fun scheme -> (scheme :> Substitutable).freeTypeVariables)
                    |> Set.unionMany

    let intType = TConstructor(Var("Int"))
    let boolType = TConstructor(Var("Bool"))

    type Applicand<'a when 'a :> Substitutable> = Applicand of 'a

    type Environment = 
        { typeVariables: TypeVariableEnv; variables: Map<Var,Scheme>; recordFields: Map<Var,TRec>; typeAliases: Map<Var,Type> }
        interface Substitutable with
            member this.Apply s =
                {
                    typeVariables = downcast (this.typeVariables :> Substitutable).Apply s;
                    variables = this.variables;
                    recordFields = this.recordFields;
                    typeAliases = this.typeAliases;
                }
                :> Substitutable
            member this.freeTypeVariables =
                (this.typeVariables :> Substitutable).freeTypeVariables

    let emptySubst: Substitution = Map.empty
    let composeSubst (s1: Substitution) (s2: Substitution) : Substitution = 
        let s1 = s1 |> Map.map (fun _ t -> downcast (t :> Substitutable).Apply s2)
        s2 
        |> Map.fold (fun s1 v t -> Map.add v t s1) s1
    let (<+) s1 s2 = composeSubst s1 s2
    let composeSubstMany (xs: Substitution seq) : Substitution =
        Seq.fold (fun s s' -> s <+ s') emptySubst xs

    let rec unify (t1: Type) (t2: Type) : Substitution =
        let occurCheck (v: TVar) (t: Substitutable) : bool =
            t.freeTypeVariables.Contains v
        let bind (v: TVar) (t: Type) = 
            match t with
            | TVariable(v') when v = v' -> emptySubst
            | t when occurCheck v t -> failwithf "Occur check failed %A -> %A" v t
            | _ -> Map.add v t emptySubst
        match t1,t2 with
        | TConstructor(c1),TConstructor(c2) when c1 = c2 -> emptySubst
        | TArrow(f1,x1),TArrow(f2,x2) -> (unify f1 f2) <+ (unify x1 x2)
        | TVariable(v),t -> bind v t
        | t,TVariable(v) -> bind v t
        | _ -> failwithf "Type mismatch %A and %A" t1 t2

    let newTyVar =
        let mutable counter = 0
        let f name =
            counter <- counter + 1
            TVariable(TVar(Var(sprintf "%s@%d" name counter)))
        f

    let instantiate (scheme: Scheme) : Type =
        let subst = Set.fold (fun s v -> Map.add v (newTyVar "a") s) emptySubst scheme.bindings
        downcast (scheme.type_ :> Substitutable).Apply subst

    let generalize (env: Environment) (type_: Type) : Scheme =
        let bindings = (type_ :> Substitutable).freeTypeVariables - (env :> Substitutable).freeTypeVariables
        { bindings = bindings; type_ = type_ }

    let generalizeM (type_: Type) : State<Environment,Scheme> =
        get |> fmap (fun e -> generalize e type_)

module TS = TypeSystem
open TS

module Thunk =
    type Thunk<'a> =   Value of 'a
                     | Thunk of (unit -> 'a)
    let evalThunk thunk =
        match !thunk with
        | Value(v) -> v
        | Thunk(t) ->
            let v = t ()
            thunk := Value v
            v

open Thunk

module Inner =
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
    and Expr = 
        { value: PlainExpr; type_: Type ref }
        interface TS.Substitutable with
            member this.Apply s =
                let value = 
                    match this.value with
                    | Literal(_) -> this.value
                    | VarRef(_) -> this.value
                    | Apply(f,xs) -> 
                        let f = downcast (f :> TS.Substitutable).Apply s
                        let xs = xs |> List.map (fun x -> downcast (x :> TS.Substitutable).Apply s)
                        Apply(f,xs)
                    | BinOp(lhs,op,rhs) ->
                        BinOp(downcast (lhs :> Substitutable).Apply s,op,downcast (rhs :> Substitutable).Apply s)
                    | If(cond,ifTrue,ifFalse) -> 
                        If(downcast (cond :> Substitutable).Apply s,downcast (ifTrue :> Substitutable).Apply s,downcast (ifFalse :> Substitutable).Apply s)
                    | RecordLiteral(fields) ->
                        fields
                        |> Map.map (fun _ e -> downcast (e :> Substitutable).Apply s)
                        |> RecordLiteral
                    | RecordAccess(obj,field) -> RecordAccess(downcast (obj :> Substitutable).Apply s,field)
                    | Fun(arguments,value) -> Fun(arguments,downcast (value :> Substitutable).Apply s)
                    | Let(name,value,body) -> Let(name,downcast (value :> Substitutable).Apply s,downcast (body :> Substitutable).Apply s)
                    | LetRec(name,value,body) -> LetRec(name,downcast (value :> Substitutable).Apply s,downcast (body :> Substitutable).Apply s)
                upcast {
                    value = value;
                    type_ = ref (downcast (!this.type_ :> TS.Substitutable).Apply s)
                }
            member this.freeTypeVariables = (!this.type_ :> TS.Substitutable).freeTypeVariables

    let updateType (x: Expr) (s: Substitution) : unit =
        x.type_ := downcast (!x.type_ :> Substitutable).Apply s
    let addVariable name scheme = yaruzo{
        let! e = get
        do! set { 
            typeVariables = e.typeVariables;
            variables = Map.add name scheme e.variables;
            recordFields = e.recordFields;
            typeAliases = e.typeAliases
        }
    }
    let apply s = yaruzo{
        do! get >>= (fun e -> set (downcast (e :> TS.Substitutable).Apply s))
    }

    type PlainDeclaration =   LetDecl of Var * Expr
                            | LetRecDecl of Var * Expr
    type Declaration = { value: PlainDeclaration; scheme: TS.Scheme }
    with
        member this.Name = 
            match this.value with
            | LetDecl(name,_) 
            | LetRecDecl(name,_) -> name
    
    let rec inferExpr (expr: AlphaTransform.Expr) : State<TS.Environment,TS.Substitution * Expr> = 
        yaruzo{
            match expr with
            | AlphaTransform.Expr.Literal(x) -> return Map.empty,{ value = Literal(x); type_ = ref (TS.intType) }
            | AlphaTransform.Expr.Apply(f,xs) -> 
                let! sf,f = inferExpr f
                let! sxs,xs = foldM (fun (s,xs) x -> yaruzo{
                                 let! s',x = inferExpr x
                                 return s <+ s',x :: xs
                              }) (TS.emptySubst,[]) xs

                let retType = newTyVar "a"
                let fType = xs |> List.fold (fun t x -> TArrow(!x.type_,t)) retType
                let suni = unify !f.type_ fType
                do! apply suni

                let subst = sf <+ sxs <+ suni
                updateType f subst
                List.fold (fun () x -> updateType x subst) () xs

                return subst,{ value = Apply(f,xs); type_ = ref (downcast (fType :> Substitutable).Apply subst) }
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
                let suni = unify (TArrow(!lhs.type_,TArrow(!rhs.type_,retType))) opType
                do! apply suni
                
                let subst = slhs <+ srhs <+ suni
                updateType lhs subst
                updateType rhs subst

                return slhs <+ srhs,{ value = BinOp(lhs,op,rhs); type_ = ref (downcast (retType :> Substitutable).Apply subst) }
            | AlphaTransform.Expr.VarRef(v) ->
                let! variables = fmap (fun e -> e.variables) get
                match variables.TryFind v with
                | None -> failwithf "variable %A not found in %A" v variables
                | Some(scheme) -> return emptySubst,{ value = VarRef(v); type_ = ref (instantiate scheme) }
            | AlphaTransform.Expr.If(cond,ifTrue,ifFalse) -> 
                let! sc,cond = inferExpr cond
                
                let subst = unify !cond.type_ (boolType)
                do! apply subst

                let! sTrue,ifTrue = inferExpr ifTrue
                let! sFalse,ifFalse = inferExpr ifFalse
                
                let subst = subst <+ unify !ifTrue.type_ !ifFalse.type_
                do! apply subst

                updateType cond subst
                updateType ifTrue subst
                updateType ifFalse subst

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
                                        let suni = unify type_ !value.type_
                                        do! apply suni
                                        return s <+ suni
                                }) emptySubst
                    let subst = s <+ s'
                    
                    Map.fold (fun () _ v -> updateType v subst) () fields

                    return subst,{ value = RecordLiteral(fields); type_ = ref (TRecord(TRec(record))) }
            | AlphaTransform.Expr.RecordAccess(obj,field) ->
                let! sobj,obj = inferExpr obj
                match !obj.type_ with
                | TRecord(TRec(record)) -> 
                    match record.TryFind field with
                    | None -> failwithf "field %A not found in %A" field record
                    | Some(type_) -> return emptySubst,{ value = RecordAccess(obj,field); type_ = ref type_ }
                | _ -> failwithf "%A is not a record" obj
            | AlphaTransform.Expr.Let(name,arguments,value,body) ->
                let arguments = List.map (fun arg -> arg,newTyVar "a") arguments
                let! sv,value = yatteiki $ yaruzo{
                    do! forEachM (fun (arg,type_) -> addVariable arg { bindings = Set.empty; type_ = type_ }) arguments
                    let! sv,value = inferExpr value
                    return sv,value
                }
                let! subst,whole = yatteiki $ yaruzo{
                    let value = 
                        if arguments.IsEmpty then value 
                        else
                            let type_ = List.foldBack (fun (_,type_) funType -> TArrow(type_,funType)) arguments !value.type_
                            let arguments = List.map fst arguments
                            { value = Fun(arguments,value); type_ = ref type_ }
                    
                    do! generalizeM !value.type_ >>= addVariable name 

                    let! sb,body = inferExpr body
                    let subst = sv <+ sb

                    updateType value subst

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
                
                let suni = unify thisType !value.type_
                do! apply suni
                updateType value suni

                let! subst,whole = yatteiki $ yaruzo{
                    let value = 
                        if arguments.IsEmpty then value 
                        else
                            let type_ = List.foldBack (fun (_,type_) funType -> TArrow(type_,funType)) arguments !value.type_
                            let arguments = List.map fst arguments
                            { value = Fun(arguments,value); type_ = ref type_ }
                    
                    do! generalizeM !value.type_ >>= addVariable name 

                    let! sb,body = inferExpr body
                    let subst = sv <+ sb

                    updateType value subst

                    return subst,{ value = Let(name,value,body); type_ = body.type_ }
                }
                return subst,whole
        }
    let inferDecl (decl: AlphaTransform.Declaration) : State<TS.Environment,Option<Declaration>> = 
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
                        typeVariables = e.typeVariables;
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
                        typeVariables = e.typeVariables;
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
                        let thisType = List.fold (fun retType (_,type_) -> TArrow(type_,retType)) !value.type_ arguments 
                        let arguments = List.map fst arguments
                        { value = Fun(arguments,value); type_ = ref thisType }

                updateType value sv
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
                        let thisType = List.fold (fun retType (_,type_) -> TArrow(type_,retType)) !value.type_ arguments 
                        let arguments = List.map fst arguments
                        { value = Fun(arguments,value); type_ = ref thisType }

                let suni = unify thisType !value.type_
                do! apply suni

                updateType value (sv <+ suni)

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