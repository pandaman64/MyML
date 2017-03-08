module AlphaTransform

open Common

type Expr =   Literal of int
            | VarRef of Var
            | Let of Var * Var list * Expr * Expr
            | LetRec of Var * Var list * Expr * Expr
            | Apply of Expr * Expr
            | If of Expr * Expr * Expr

type Declaration =   LetDecl of Var * Var list * Expr
                   | LetRecDecl of Var * Var list * Expr

type Environment = Map<Var,Expr>

let newVar =
    let mutable counter = 0
    let impl name =
        counter <- counter + 1
        Var(sprintf "%s@%d" name counter)
    impl

let rec alphaTransformExpr (env: Environment) (expr: Parser.Expr): Expr = 
    match expr with
    | Parser.Expr.Literal(x) -> Literal(x)
    | Parser.Expr.If(cond,ifTrue,ifFalse) -> 
        If(alphaTransformExpr env cond,alphaTransformExpr env ifTrue,alphaTransformExpr env ifFalse)
    | Parser.Expr.Apply(f,xs) -> //currying
        List.fold (fun f x -> Apply(f,alphaTransformExpr env x)) (alphaTransformExpr env f) xs
    | Parser.Expr.Let(name,argument,value,body) -> 
        let argumentVars = List.map newVar argument
        let value = 
            let argumentRefs = List.map VarRef argumentVars
            let newEnv = Seq.zip (List.map Var argument) argumentRefs
                         |> Map.ofSeq
            let env = mergeMap newEnv env
            alphaTransformExpr env value
        let thisVar = newVar name
        let body = 
            let thisRef = VarRef(thisVar)
            let env = Map.add (Var(name)) thisRef env
            alphaTransformExpr env body
        Let(thisVar,argumentVars,value,body)
    | Parser.Expr.LetRec(name,argument,value,body) -> 
        let thisVar = newVar name
        let thisRef = VarRef(thisVar)
        let env = Map.add (Var(name)) thisRef env

        let argumentVars = List.map newVar argument
        let value =
            let argumentRefs = List.map VarRef argumentVars
            let newEnv = Seq.zip (List.map Var argument) argumentRefs
                         |> Map.ofSeq
            let env = mergeMap newEnv env
            alphaTransformExpr env value
        let body = alphaTransformExpr env body
        LetRec(thisVar,argumentVars,value,body)
    | Parser.Expr.Identifier(name) -> 
        match env.TryFind (Var(name)) with
        | None ->
            failwithf "variable '%s' not found in %A" name env 
            //VarRef(newVar (sprintf "%s_notfound" name))
        | Some(expr) -> expr

let alphaTransformDecl (env: Environment) (expr: Parser.Declaration): Declaration =
    match expr with
    | Parser.Declaration.LetDecl(name,argument,value) ->
        let argumentVars = List.map newVar argument
        let argumentRefs = List.map VarRef argumentVars
        let env = 
            let newEnv = Seq.zip (List.map Var argument) argumentRefs
                         |> Map.ofSeq
            mergeMap newEnv env
        let value = alphaTransformExpr env value
        LetDecl(Var(name),argumentVars,value)
    | Parser.Declaration.LetRecDecl(name,argument,value) ->
        let thisVar = Var(name)
        let thisRef = VarRef(thisVar)
        let argumentVars = List.map newVar argument
        let argumentRefs = List.map VarRef argumentVars
        let env =
            let newEnv = Seq.zip (List.map Var argument) argumentRefs
                         |> Map.ofSeq
                         |> Map.add (Var(name)) thisRef
            mergeMap newEnv env
        let value = alphaTransformExpr env value
        LetRecDecl(thisVar,argumentVars,value)

let alphaTransformDecls externs decls =
    let env = 
        Set.map (fun name -> (Var(name),VarRef(Var(name)))) externs
        |> Map.ofSeq
    let impl (env,decls) decl =
        let declVar = 
            match decl with
            | Parser.Declaration.LetDecl(name,_,_) -> Var(name)
            | Parser.Declaration.LetRecDecl(name,_,_) -> Var(name)
        let decl = alphaTransformDecl env decl
        (Map.add declVar (VarRef(declVar)) env,decl :: decls)
    let _,decls = List.fold impl (env,[]) decls
    List.rev decls