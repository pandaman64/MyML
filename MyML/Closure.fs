﻿module Closure

open Common

let freeVariablesString freeVariables =
    freeVariables
    |> Seq.map (fun (Var(v)) -> sprintf "%s" v)
    |> String.concat " "

type AlphaTransform.Expr
with
    member this.freeVariables: Set<Var> = 
        match this with
        | AlphaTransform.Expr.Literal(_) -> Set.empty
        | AlphaTransform.Expr.VarRef(x) -> Set.singleton x
        | AlphaTransform.Expr.If(cond,ifTrue,ifFalse) ->
            Set.unionMany [cond.freeVariables; ifTrue.freeVariables; ifFalse.freeVariables]
        | AlphaTransform.Expr.Apply(f,xs) ->
            xs
            |> List.map (fun x -> x.freeVariables)
            |> cons f.freeVariables
            |> Set.unionMany
        | AlphaTransform.Expr.Let(name,argument,value,body) ->
            let argument = Set.ofList argument
            let value = value.freeVariables - argument
            let body = body.freeVariables
            Set.union value body - Set.singleton name
        | AlphaTransform.Expr.LetRec(name,argument,value,body) ->
            let argument = name :: argument |> Set.ofList
            let value = value.freeVariables - argument
            let body = body.freeVariables
            Set.union value body - Set.singleton name
        | AlphaTransform.Expr.BinOp(lhs,_,rhs) ->
            Set.union lhs.freeVariables rhs.freeVariables
        | AlphaTransform.Expr.RecordLiteral(fields) ->
            Map.toSeq fields
            |> Seq.map snd
            |> Seq.map (fun expr -> expr.freeVariables)
            |> Set.unionMany
        | AlphaTransform.Expr.RecordAccess(obj,_) -> obj.freeVariables

type RecordType = RecordType of Var * Map<Var,Signature>
// name * body * record type
type Closure = Closure of Var * Function * RecordType
with
    member this.Name =
        let (Closure(name,_,_)) = this
        name
and
    [<StructuredFormatDisplayAttribute("{AsString}")>]
    Expr =   Literal of int
           | ExternRef of Var
           | Alias of Var * Expr * Expr
           | AliasRec of Var * Expr * Expr
           | Apply of Expr * Expr list
           | If of Expr * Expr * Expr
           | BinOp of Expr * Operator * Expr
           | RecordLiteral of Var option * Map<Var,Expr> // name(option) * fields
           | RecordAccess of Expr * Var
    with
        member this.freeVariables (locals: Map<Var,Declaration>): Set<Var> = 
            match this with
            | Literal(_) -> Set.empty
            | ExternRef(var) -> 
                match locals.TryFind var with
                | None -> Set.empty
                | Some(decl) -> Set.singleton decl.Name
            | Alias(v,value,body) -> 
                Set.union (value.freeVariables locals) (body.freeVariables locals) - Set.singleton v
            | AliasRec(v,value,body) ->
                Set.union (value.freeVariables locals) (body.freeVariables locals) - Set.singleton v
            | Apply(f,xs) -> 
                xs
                |> List.map (fun x -> x.freeVariables locals)
                |> cons (f.freeVariables locals)
                |> Set.unionMany
            | If(cond,ifTrue,ifFalse) ->
                [cond; ifTrue; ifFalse]
                |> List.map (fun x -> x.freeVariables locals)
                |> Set.unionMany 
            | BinOp(lhs,_,rhs) ->
                Set.union (lhs.freeVariables locals) (rhs.freeVariables locals)
            | RecordLiteral(_,fields) ->
                fields
                |> Map.toSeq
                |> Seq.map snd
                |> Seq.map (fun expr -> expr.freeVariables locals)
                |> Set.unionMany
            | RecordAccess(obj,_) -> obj.freeVariables locals
        override this.ToString() =
            match this with
            | Literal(x) -> sprintf "%d" x
            | ExternRef(Var(x)) -> x
            | Alias(Var(name),value,body) -> 
                sprintf "alias %s = %A in %A" name value body
            | AliasRec(Var(name),value,body) -> 
                sprintf "alias rec %s = %A in %A" name value body
            | Apply(f,x) ->
                sprintf "(%A %A)" f x
            | If(cond,ifTrue,ifFalse) ->
                sprintf "if %A then %A else %A" cond ifTrue ifFalse
            | BinOp(lhs,op,rhs) -> sprintf "(%A %A %A)" lhs op rhs
            | RecordLiteral(name,fields) ->
                let fieldsString = fields
                                   |> Map.toSeq
                                   |> Seq.map (fun (Var(name),value) -> sprintf "%s = %A" name value)
                                   |> String.concat "; "
                match name with
                | None -> sprintf "{ %s }" fieldsString
                | Some(Var(name)) -> sprintf "%s { %s }" name fieldsString
            | RecordAccess(obj,Var(field)) -> sprintf "(%A).%s" obj field
        member this.AsString = this.ToString()
and
    Function = {argument: Var list; body: Expr}
and
    TypeDecl =   Record of RecordType
               | TyAlias of Var * Signature
    with
        member this.Name =
            match this with
            | Record(RecordType(name,_)) -> name
            | TyAlias(name,_) -> name
and
    [<StructuredFormatDisplayAttribute("{AsString}")>]
    Declaration =    FreeValue of Var * Expr
                   | FreeFunction of Var * Function
                   | FreeRecFunction of Var * Function
                   | ClosureDecl of Closure
                   | ClosureRecDecl of Closure
                   | TypeDecl of TypeDecl
    with
        member this.Name: Var = 
            match this with
            | FreeValue(name,_) -> name
            | FreeFunction(name,_) -> name
            | FreeRecFunction(name,_) -> name
            | ClosureDecl(cls) -> cls.Name
            | ClosureRecDecl(cls) -> cls.Name
            | TypeDecl(decl) -> decl.Name
        override this.ToString() =
            match this with
            | FreeValue(Var(name),expr) -> sprintf "value %s = %A" name expr
            | FreeFunction(Var(name),{argument = argument; body = body}) ->
                sprintf "function %s %A = %A" name argument body
            | FreeRecFunction(Var(name),{argument = argument; body = body}) ->
                sprintf "function rec %s %A = %A" name argument body
            | ClosureDecl(Closure(Var(name),{argument = argument; body = body},clsType)) ->
                sprintf "closure %s %A {%A} = %A" name argument clsType body
            | ClosureRecDecl(Closure(Var(name),{argument = argument; body = body},clsType)) ->
                sprintf "closure rec %s %A {%A} = %A" name argument clsType body
            | TypeDecl(decl) ->
                sprintf "type %A = %A" this.Name decl
        member this.AsString = this.ToString()

let newVar =
    let mutable counter = 0
    let func (Var(name)): Var =
        counter <- counter + 1
        Var(sprintf "%s_%d" name counter)
    func

let unionMap m1 m2 =
    Map.fold (fun m k v -> Map.add k v m) m1 m2

let unionMapMany ms =
    List.fold unionMap Map.empty ms

let addArgumentToEnvironment (argument: Var list) (externs: Map<Var,Declaration>) =
    List.fold (fun externs argument -> Map.add argument (FreeValue(argument,ExternRef(argument))) externs) externs argument

let rec applyFreeVariables (externs: Map<Var,Declaration>) (name: Var) (freeVariables: Set<Var>): Expr =
    let folder applications var =
        match externs.TryFind var with
        | Some(ClosureDecl(Closure(_,_,RecordType(_,clsType)))) -> 
            let freeVariables = clsType |> Map.toSeq |> Seq.map fst |> Set.ofSeq
            let value = applyFreeVariables externs name freeVariables
            Map.add var value applications
        | Some(decl) -> Map.add var (ExternRef(var)) applications
        | None -> applications
    let applications = Set.fold folder Map.empty freeVariables
    let clsRecord = 
        match externs.TryFind name with
        | None -> failwith "not found"
        | Some(ClosureDecl(Closure(_,_,RecordType(name,_)))) -> RecordLiteral(Some(name),applications)
        | Some(ClosureRecDecl(Closure(_,_,RecordType(name,_)))) -> RecordLiteral(Some(name),applications)
        | _ -> failwith "?"
    Apply(ExternRef(name),[clsRecord])

let capturedVariables (argument: Var list) (value: Expr) (locals: Map<Var,Declaration>): Set<Var> =
    let localVariables = Map.toSeq locals
                            |> Seq.map fst
                            |> Set.ofSeq
    let argument = Set.ofList argument
    (Set.intersect (value.freeVariables locals) localVariables) - argument

let makeFunctionDecl (name: Var) (argument: Var list) (value: Expr) (locals: Map<Var,Declaration>) (isRecursive: bool): Declaration list =
    let freeCtor,closureCtor =
        if isRecursive then FreeRecFunction,ClosureRecDecl
        else FreeFunction,ClosureDecl
    // the argument is bound in this binding
    let freeVariables = value.freeVariables locals - Set.ofList argument
    if freeVariables.IsEmpty then 
        // the function does not have free variables 
        // thus we can treat this as a free function

        // both 'name' and 'argument' are unique identifiers, 
        // so simply reusing them will not affect the uniqueness of identifiers
        // (maybe helpful for debugging if we append the function name to the name of this binding?) 
        [freeCtor (name,{argument = argument; body = value})]
    else
        // the function has free varibales
        // thus we have to treat this as a closure

        // captured variables of the closure have the same name in the original scope. 
        // thus the uniqueness of identifiers will be broken after closure transformation
        // but we just ignore them

        // make new record type for this closure
        let (Var(nameString)) = name
        let clsType = freeVariables
                      |> Set.toSeq
                      |> Seq.map (fun (Var(v)) -> Var(sprintf "%s" v), SigTyVar(newVar (Var("a"))))
                      |> Map.ofSeq
                      |> fun x -> RecordType(Var(sprintf "%s__closure__type" nameString),x)

        [
            closureCtor (Closure(name,{argument = argument; body = value},clsType));
            TypeDecl(Record(clsType)); 
        ]

let rec extractDeclarations (externs: Map<Var,Declaration>) (locals: Map<Var,Declaration>) (expr: AlphaTransform.Expr): Declaration list * Expr = 
    match expr with
    | AlphaTransform.Expr.Literal(x) -> 
        List.empty,Literal(x)
    | AlphaTransform.Expr.If(cond,ifTrue,ifFalse) -> 
        let declCond,cond = extractDeclarations externs locals cond
        let declTrue,ifTrue = extractDeclarations externs locals ifTrue
        let declFalse,ifFalse = extractDeclarations externs locals ifFalse
        List.concat [declCond; declTrue; declFalse],If(cond,ifTrue,ifFalse)
    | AlphaTransform.Expr.BinOp(lhs,op,rhs) -> 
        let declLhs,lhs = extractDeclarations externs locals lhs
        let declRhs,rhs = extractDeclarations externs locals rhs
        List.append declLhs declRhs,BinOp(lhs,op,rhs)
    | AlphaTransform.Expr.Apply(f,xs) ->
        let declF,f = extractDeclarations externs locals f
        let declX,xs = List.map (extractDeclarations externs locals) xs
                       |> List.unzip 
        List.concat (declF :: declX),Apply(f,xs)
    | AlphaTransform.Expr.Let(name,argument,value,body) ->
        let declValue,value = 
            let locals = addArgumentToEnvironment argument locals
            extractDeclarations externs locals value
        match argument with
        | [] -> 
            // if this let binding is alias, it will not escape from the scope, 
            // so we don't treat it as closures 
            let locals = Map.add name (FreeValue(name,value)) locals
            let declBody,body = extractDeclarations externs locals body
            List.append declValue declBody,Alias(name,value,body)
        | argument -> 
            // if the value of this let binding has free variables, those may escape from the scope,
            // so we need to declare the function as a closure
            let decls = makeFunctionDecl name argument value locals false

            let declBody,body = 
                let externs = decls |> List.fold (fun externs decl -> Map.add decl.Name decl externs) externs 
                extractDeclarations externs locals body
                
            // lift this let binding to the global scope
            let newGlobals = List.concat [ decls; declValue; declBody ]

            // this let binding will be lifted to the global scope, 
            // so 'body' will be the evaluation of this expression
            newGlobals,body
    | AlphaTransform.Expr.LetRec(name,argument,value,body) ->
        // first, we assume this binding forms a free function
        let declValue,value' = 
            let externs = Map.add name (FreeValue(name,ExternRef(name))) externs
            let locals = addArgumentToEnvironment argument locals
            extractDeclarations externs locals value
        match argument with
        | [] -> 
            // if this let binding is alias, it will not escape from the scope, 
            // so we don't treat it as closures 
            let locals = Map.add name (FreeValue(name,value')) locals
            let declBody,body = extractDeclarations externs locals body
            List.append declValue declBody,AliasRec(name,value',body)
        | argument -> 
            // Now that we know the value of this let binding must be a closure,
            // thus we have to extract it in the suitable environment
            
            // closure application rules can be computed from the former trial,
            // we use this inside the recursive function
            let rule = capturedVariables argument value' locals

            let declValue,value = 
                // the value must be in the local environment!
                // we fill the unknown body with placeholders
                let locals =  locals
                              |> Map.add name 
                                 (ClosureRecDecl(Closure(name,{argument = [Var("placeholder")]; body = ExternRef(Var("placeholder'"))},RecordType(Var("placeholder''"),Map.empty))))
                let locals = 
                    argument
                    |> List.fold (fun locals argument -> Map.add argument (FreeValue(argument,ExternRef(argument))) locals) locals
                extractDeclarations externs locals value
            
            let decls = makeFunctionDecl name argument value locals true

            // if lifted declaration is free, 
            // all appearances of value itself in value must be changed into naked ExternRef
            // but we ignore this now

            let declBody,body = 
                let externs = decls |> List.fold (fun externs decl -> Map.add decl.Name decl externs) externs
                extractDeclarations externs locals body
                
            // lift this let binding to the global scope
            let newGlobals = List.concat [ decls; declValue; declBody ]

            // this let binding will be lifted to the global scope, 
            // so 'body' will be the evaluation of this expression
            newGlobals,body
    | AlphaTransform.Expr.VarRef(name) ->
        let variables = unionMap externs locals
        match variables.TryFind name with
        | Some(ClosureDecl(Closure(name,_,RecordType(_,clsType)))) -> 
            let freeVariables = clsType |> Map.toSeq |> Seq.map fst |> Set.ofSeq
            List.empty,applyFreeVariables variables name freeVariables
        | Some(ClosureRecDecl(Closure(name,_,RecordType(_,clsType)))) -> 
            let freeVariables = clsType |> Map.toSeq |> Seq.map fst |> Set.ofSeq
            List.empty,applyFreeVariables variables name freeVariables
        | Some(decl) -> List.empty,ExternRef(decl.Name)
        | None ->
            printfn "%A not found in the scope" name 
            List.empty,ExternRef(name)
    | AlphaTransform.Expr.RecordLiteral(fields) -> 
        fields
        |> Map.toSeq
        |> Seq.map (fun (name,expr) -> name,extractDeclarations externs locals expr)
        |> Seq.fold (fun (decls,fields) (name,(decls',expr)) -> (List.append decls decls',Map.add name expr fields)) ([],Map.empty)
        |> fun (decls,fields) -> decls,RecordLiteral(None,fields)
    | AlphaTransform.Expr.RecordAccess(obj,field) -> 
        let decls,obj = extractDeclarations externs locals obj
        decls,RecordAccess(obj,field)

let transformDecl (externs: Map<Var,Declaration>) (decl: AlphaTransform.Declaration): Declaration list =
    match decl with
    | AlphaTransform.Declaration.LetDecl(name,argument,value) -> 
        let decls,expr =
            let locals = argument
                         |> List.map (fun name -> name,FreeValue(name,ExternRef(name)))
                         |> Map.ofList
            extractDeclarations externs locals value
        let decl =
            match argument with
            | [] ->
                FreeValue(name,expr)
            | argument -> 
                FreeFunction(name,{argument = argument; body = expr})
        decl :: decls
        |> List.rev // extracted declarations must come first because the body of 'decl' may depend on those declarations
    | AlphaTransform.Declaration.LetRecDecl(name,argument,value) -> 
        let decls,expr =
            let externs = Map.add name (FreeValue(name,ExternRef(name))) externs
            let locals = argument
                         |> List.map (fun name -> name,FreeValue(name,ExternRef(name)))
                         |> Map.ofList
            extractDeclarations externs locals value
        let decl =
            match argument with
            | [] ->
                FreeValue(name,expr)
            | argument -> 
                FreeRecFunction(name,{argument = argument; body = expr})
        decl :: decls
        |> List.rev // extracted declarations must come first because the body of 'decl' may depend on those declarations
    | AlphaTransform.Declaration.TypeDecl(name,decl) ->
        let decl = match decl with
                   | AlphaTransform.TyAlias(alias) -> TyAlias(name,alias)
                   | AlphaTransform.Record(fields) -> Record(RecordType(name,fields))
        [TypeDecl(decl)]

let transformDecls (externs: Var seq) (decls: AlphaTransform.Declaration seq): Declaration list =
    let externs = 
        externs
        |> Seq.map (fun variable -> variable,FreeValue(variable,ExternRef(variable)))
        |> Map.ofSeq
    let folder (externs,decls) decl =
        let newDecls = transformDecl externs decl
        let externs = newDecls 
                      |> List.map (fun (decl: Declaration) -> decl.Name,decl)
                      |> Map.ofList
                      |> unionMap externs
        externs,List.append decls newDecls
    Seq.fold folder (externs,List.empty) decls
    |> snd