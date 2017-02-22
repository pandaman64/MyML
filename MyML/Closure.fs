module Closure

let Var = AlphaTransform.Var
type Var = AlphaTransform.Var

let freeVariablesString freeVariables =
    freeVariables
    |> Seq.map (fun ((AlphaTransform.Var(v))) -> sprintf "%s" v)
    |> String.concat " "

type AlphaTransform.Expr
with
    member this.freeVariables: Set<Var> = 
        match this with
        | AlphaTransform.Expr.Literal(_) -> Set.empty
        | AlphaTransform.Expr.VarRef(x) -> Set.singleton x
        | AlphaTransform.Expr.If(cond,ifTrue,ifFalse) ->
            Set.unionMany [cond.freeVariables; ifTrue.freeVariables; ifFalse.freeVariables]
        | AlphaTransform.Expr.Apply(f,x) ->
            Set.union f.freeVariables x.freeVariables
        | AlphaTransform.Expr.Let(name,argument,value,body) ->
            let argument = Option.toList argument |> Set.ofList
            let value = value.freeVariables - argument
            let body = body.freeVariables
            Set.union value body - Set.singleton name
        | AlphaTransform.Expr.LetRec(name,argument,value,body) ->
            let argument = name :: Option.toList argument |> Set.ofList
            let value = value.freeVariables - argument
            let body = body.freeVariables
            Set.union value body - Set.singleton name

// name * body * captured variables
type Closure = Closure of Var * Function * Set<Var>
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
           | Apply of Expr * Expr
           | ApplyClosure of Expr * Map<Var,Expr> 
           | If of Expr * Expr * Expr
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
            | Apply(f,x) -> Set.union (f.freeVariables locals) (x.freeVariables locals)
            | ApplyClosure(closure,application) ->
                let keys = Map.toSeq application
                           |> Seq.map fst
                           |> Set.ofSeq
                closure.freeVariables locals - keys
            | If(cond,ifTrue,ifFalse) ->
                [cond; ifTrue; ifFalse]
                |> List.map (fun x -> x.freeVariables locals)
                |> Set.unionMany 
        override this.ToString() =
            match this with
            | Literal(x) -> sprintf "%d" x
            | ExternRef(AlphaTransform.Var(x)) -> x
            | Alias(AlphaTransform.Var(name),value,body) -> 
                sprintf "alias %s = %A in %A" name value body
            | AliasRec(AlphaTransform.Var(name),value,body) -> 
                sprintf "alias rec %s = %A in %A" name value body
            | Apply(f,x) ->
                sprintf "(%A %A)" f x
            | ApplyClosure(cls,application) -> 
                let applicationString = application
                                        |> Map.toSeq
                                        |> Seq.map (fun (AlphaTransform.Var(name),value) -> sprintf "%s -> %A" name value)
                                        |> String.concat " "
                sprintf "[%A {%s}]" cls applicationString
            | If(cond,ifTrue,ifFalse) ->
                sprintf "if %A then %A else %A" cond ifTrue ifFalse
        member this.AsString = this.ToString()
and
    Function = {argument: Var; body: Expr}
and
    [<StructuredFormatDisplayAttribute("{AsString}")>]
    Declaration =    FreeValue of Var * Expr
                   | FreeFunction of Var * Function
                   | FreeRecFunction of Var * Function
                   | ClosureDecl of Closure
    with
        member this.Name: Var = 
            match this with
            | FreeValue(name,_) -> name
            | FreeFunction(name,_) -> name
            | FreeRecFunction(name,_) -> name
            | ClosureDecl(cls) -> cls.Name
        override this.ToString() =
        
            match this with
            | FreeValue(AlphaTransform.Var(name),expr) -> sprintf "value %s = %A" name expr
            | FreeFunction(AlphaTransform.Var(name),{argument = AlphaTransform.Var(argument); body = body}) ->
                sprintf "function %s %s = %A" name argument body
            | FreeRecFunction(AlphaTransform.Var(name),{argument = AlphaTransform.Var(argument); body = body}) ->
                sprintf "function rec %s %s = %A" name argument body
            | ClosureDecl(Closure(AlphaTransform.Var(name),{argument = AlphaTransform.Var(argument); body = body},freeVariables)) ->
                sprintf "closure %s %s {%s} = %A" name argument (freeVariablesString freeVariables) body
        member this.AsString = this.ToString()

let newVar =
    let mutable counter = 0
    let func (AlphaTransform.Var(name)): Var =
        counter <- counter + 1
        Var(sprintf "%s_%d" name counter)
    func

let unionMap m1 m2 =
    Map.fold (fun m k v -> Map.add k v m) m1 m2

let unionMapMany ms =
    List.fold unionMap Map.empty ms

let addArgumentToEnvironment (argument: Option<Var>) (externs: Map<Var,Declaration>) =
    match argument with
    | None -> externs
    | Some(argument) -> Map.add argument (FreeValue(argument,ExternRef(argument))) externs

let rec applyFreeVariables (externs: Map<Var,Declaration>) (name: Var) (freeVariables: Set<Var>): Expr =
    let folder applications var =
        match externs.TryFind var with
        | Some(ClosureDecl(Closure(_,_,freeVariables))) -> 
            let value = applyFreeVariables externs name freeVariables
            Map.add var value applications
        | Some(decl) -> Map.add var (ExternRef(var)) applications
        | None -> applications
    let applications = Set.fold folder Map.empty freeVariables
    ApplyClosure(ExternRef(name),applications)

let capturedVariables (argument: Var) (value: Expr) (locals: Map<Var,Declaration>): Set<Var> =
    let localVariables = Map.toSeq locals
                            |> Seq.map fst
                            |> Set.ofSeq
    let argument = Set.singleton argument
    (Set.intersect (value.freeVariables locals) localVariables) - argument

let makeFunctionDecl (name: Var) (argument: Var) (value: Expr) (locals: Map<Var,Declaration>): Declaration =
    // the argument is bound in this binding
    let freeVariables = value.freeVariables locals - Set.singleton argument
    if freeVariables.IsEmpty then 
        // the function does not have free variables 
        // thus we can treat this as a free function

        // both 'name' and 'argument' are unique identifiers, 
        // so simply reusing them will not affect the uniqueness of identifiers
        // (maybe helpful for debugging if we append the function name to the name of this binding?) 
        FreeFunction(name,{argument = argument; body = value})
    else
        // the function has free varibales
        // thus we have to treat this as a closure

        // captured variables of the closure have the same name in the original scope. 
        // thus the uniqueness of identifiers will be broken after closure transformation
        // but we just ignore them
        ClosureDecl(Closure(name,{argument = argument; body = value},freeVariables))

let rec extractDeclarations (externs: Map<Var,Declaration>) (locals: Map<Var,Declaration>) (expr: AlphaTransform.Expr): Declaration list * Expr = 
    match expr with
    | AlphaTransform.Expr.Literal(x) -> 
        List.empty,Literal(x)
    | AlphaTransform.Expr.If(cond,ifTrue,ifFalse) -> 
        let declCond,cond = extractDeclarations externs locals cond
        let declTrue,ifTrue = extractDeclarations externs locals ifTrue
        let declFalse,ifFalse = extractDeclarations externs locals ifFalse
        List.concat [declCond; declTrue; declFalse],If(cond,ifTrue,ifFalse)
    | AlphaTransform.Expr.Apply(f,x) ->
        let declF,f = extractDeclarations externs locals f
        let declX,x = extractDeclarations externs locals x
        List.append declF declX,Apply(f,x)
    | AlphaTransform.Expr.Let(name,argument,value,body) ->
        let declValue,value = 
            let locals = addArgumentToEnvironment argument locals
            extractDeclarations externs locals value
        match argument with
        | None -> 
            // if this let binding is alias, it will not escape from the scope, 
            // so we don't treat it as closures 
            let locals = Map.add name (FreeValue(name,value)) locals
            let declBody,body = extractDeclarations externs locals body
            List.append declValue declBody,Alias(name,value,body)
        | Some(argument) -> 
            // if the value of this let binding has free variables, those may escape from the scope,
            // so we need to declare the function as a closure
            let decl = makeFunctionDecl name argument value locals

            let declBody,body = 
                let externs = Map.add name decl externs
                extractDeclarations externs locals body
                
            // lift this let binding to the global scope
            let newGlobals = decl :: List.append declValue declBody

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
        | None -> 
            // if this let binding is alias, it will not escape from the scope, 
            // so we don't treat it as closures 
            let locals = Map.add name (FreeValue(name,value')) locals
            let declBody,body = extractDeclarations externs locals body
            List.append declValue declBody,Alias(name,value',body)
        | Some(argument) -> 
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
                                 (ClosureDecl(Closure(name,{argument = Var("placeholder"); body = ExternRef(Var("placeholder'"))},rule)))
                let locals = Map.add argument (FreeValue(argument,ExternRef(argument))) locals
                extractDeclarations externs locals value
            
            let decl = makeFunctionDecl name argument value locals

            let declBody,body = 
                let externs = Map.add name decl externs
                extractDeclarations externs locals body
                
            // lift this let binding to the global scope
            let newGlobals = decl :: List.append declValue declBody

            // this let binding will be lifted to the global scope, 
            // so 'body' will be the evaluation of this expression
            newGlobals,body
    | AlphaTransform.Expr.VarRef(name) ->
        let variables = unionMap externs locals
        match variables.TryFind name with
        | Some(ClosureDecl(Closure(name,_,freeVariables))) -> 
            List.empty,applyFreeVariables variables name freeVariables
        | Some(decl) -> List.empty,ExternRef(decl.Name)
        | None ->
            printfn "%A not found in the scope" name 
            List.empty,ExternRef(name)

let transformDecl (externs: Map<Var,Declaration>) (decl: AlphaTransform.Declaration): Declaration list =
    match decl with
    | AlphaTransform.Declaration.LetDecl(name,argument,value) -> 
        let decls,expr =
            let locals = argument
                         |> Option.map (fun name -> name,FreeValue(name,ExternRef(name)))
                         |> Option.toList
                         |> Map.ofList
            extractDeclarations externs locals value
        let decl =
            match argument with
            | Some(argument) -> 
                FreeFunction(name,{argument = argument; body = expr})
            | None ->
                FreeValue(name,expr)
        decl :: decls
        |> List.rev // extracted declarations must come first because the body of 'decl' may depend on those declarations
    | AlphaTransform.Declaration.LetRecDecl(name,argument,value) -> 
        let decls,expr =
            let externs = Map.add name (FreeValue(name,ExternRef(name))) externs
            let locals = argument
                         |> Option.map (fun name -> name,FreeValue(name,ExternRef(name)))
                         |> Option.toList
                         |> Map.ofList
            extractDeclarations externs locals value
        let decl =
            match argument with
            | Some(argument) -> 
                FreeFunction(name,{argument = argument; body = expr})
            | None ->
                FreeValue(name,expr)
        decl :: decls
        |> List.rev // extracted declarations must come first because the body of 'decl' may depend on those declarations

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