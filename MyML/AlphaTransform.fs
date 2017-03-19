module AlphaTransform

open Common

type Expr =   Literal of int
            | VarRef of Var
            | Let of Var * Var list * Expr * Expr
            | LetRec of Var * Var list * Expr * Expr
            | Apply of Expr * Expr list
            | If of Expr * Expr * Expr
            | BinOp of Expr * Operator * Expr
            | RecordLiteral of Map<Var,Expr>
            | RecordAccess of Expr * Var

let rec sigTransform signature =
    match signature with
    | Parser.SigLiteral(x) -> SigLiteral(Var(x))
    | Parser.SigArrow(lhs,rhs) -> SigArrow(sigTransform lhs,sigTransform rhs)

type TypeDecl =   Record of Map<Var,Signature>
                | TyAlias of Signature

type Declaration =   LetDecl of Var * Var list * Expr
                   | LetRecDecl of Var * Var list * Expr
                   | TypeDecl of Var * TypeDecl

type Environment = Map<Var,Expr>

let newVar =
    let mutable counter = 0
    let impl name =
        counter <- counter + 1
        Var(sprintf "%s@%d" name counter)
    impl

let rec alphaTransformExpr (env: Environment) (expr: Parser.Expr): Expr = 
    match expr with
    | Parser.Expr.IntegerLiteral(x) -> Literal(x)
    | Parser.Expr.If(cond,ifTrue,ifFalse) -> 
        If(alphaTransformExpr env cond,alphaTransformExpr env ifTrue,alphaTransformExpr env ifFalse)
    | Parser.Expr.Apply(f,xs) -> Apply(alphaTransformExpr env f,List.map (alphaTransformExpr env) xs)
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
    | Parser.Expr.BinOp(lhs,op,rhs) -> BinOp(alphaTransformExpr env lhs,op,alphaTransformExpr env rhs)
    | Parser.Expr.RecordLiteral(fields) -> 
        let fields = Map.toSeq fields
                     |> Seq.map (fun (name,value) -> Var(name),alphaTransformExpr env value)
                     |> Map.ofSeq
        RecordLiteral(fields)
    | Parser.Expr.RecordAccess(obj,field) ->
        RecordAccess(alphaTransformExpr env obj,Var(field))

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
    | Parser.Declaration.TypeDecl(name,decl) ->
        let decl = match decl with
                   | Parser.TyAlias(alias) -> TyAlias(sigTransform alias)
                   | Parser.Record(fields) -> Map.toSeq fields
                                              |> Seq.map (fun (x,y) -> Var(x),sigTransform y)
                                              |> Map.ofSeq
                                              |> Record
        TypeDecl(Var(name),decl)

let alphaTransformDecls externs decls =
    let env = 
        Set.map (fun name -> (Var(name),VarRef(Var(name)))) externs
        |> Map.ofSeq
    let impl (env,decls) decl =
        let declVar = 
            match decl with
            | Parser.Declaration.LetDecl(name,_,_) -> Var(name)
            | Parser.Declaration.LetRecDecl(name,_,_) -> Var(name)
            | Parser.Declaration.TypeDecl(name,_) -> Var(name)
        let decl = alphaTransformDecl env decl
        (Map.add declVar (VarRef(declVar)) env,decl :: decls)
    let _,decls = List.fold impl (env,[]) decls
    List.rev decls