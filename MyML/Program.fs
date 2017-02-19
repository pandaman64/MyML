//写経元: https://gist.github.com/praeclarum/5fbef41ea9c296590f23

module Program

open FParsec
open Parser

type Var = Var of string

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Expr' =   Num of int
             | VarRef of Var
             | Fun of Var * Expr'
             | Let' of Var * Expr' * Expr'
             | LetRec' of Var * Expr' * Expr'
             | Apply' of Expr' * Expr'
             | If' of Expr' * Expr' * Expr'
with
    override this.ToString() =
        match this with
        | Num(x) -> sprintf "%d" x
        | VarRef(Var(name)) -> sprintf "'%s'" name
        | Fun(Var(name),expr) -> sprintf "(fun '%s' -> %A)" name expr
        | Let'(Var(name),value,inValue) -> sprintf "let '%s' = %A in %A" name value inValue
        | LetRec'(Var(name),value,inValue) -> sprintf "let rec '%s' = %A in %A" name value inValue
        | Apply'(f,x) -> sprintf "(%A %A)" f x
        | If'(cond,ifTrue,ifFalse) -> sprintf "if %A then %A else %A" cond ifTrue ifFalse
    member this.AsString = this.ToString()

module Environment =
    type Environment = Map<Var,Expr'>
    let empty:Environment = Map.empty
    let add = Map.add
    let rec tryFind = Map.tryFind
    let newVar =
        let mutable counter = 0
        let var v =
            counter <- counter + 1
            Var(sprintf "%s@%d" v counter)
        var

let rec transformExpr env expr =
    match expr with
    | Literal(x) -> Num(x)
    | If(cond,ifTrue,ifFalse) -> If'(transformExpr env cond,transformExpr env ifTrue,transformExpr env ifFalse)
    | Apply(f,xs) -> //currying
        match xs with
        | [] -> transformExpr env f
        | xs ->
            let rec curry f xs =
                match xs with
                | [] -> f
                | x::xs -> curry (Apply'(f,x)) xs 
            curry (transformExpr env f) (List.map (transformExpr env) xs)
    | Identifier(name) -> 
        match Environment.tryFind (Var(name)) env with
        //| None -> printfn "variable %s not found in %A" name env;failwith "variable not found"
        | None -> 
            printfn "variable not found '%s' in %A.\nType information of '%s' must be supplied later." name env name;
            VarRef(Var(name))
        | Some(e) -> e
    | Let(thisName,argName,value,inValue) -> 
        match argName with
        | None -> //alias
            let value' = transformExpr env value
            let thisVar = Environment.newVar thisName
            let newEnv = Environment.add (Var(thisName)) (VarRef(thisVar)) env
            Let'(thisVar,value',transformExpr newEnv inValue)
        | Some(x) -> //function definition
            let this = 
                let xVar = Environment.newVar x
                let value' = 
                    let innerEnv = Environment.add (Var(x)) (VarRef(xVar)) env
                    transformExpr innerEnv value
                Fun(xVar,value')
            let thisVar = Environment.newVar thisName
            let newEnv = Environment.add (Var(thisName)) (VarRef(thisVar)) env
            Let'(thisVar,this,transformExpr newEnv inValue)
    | LetRec(thisName,argName,value,inValue) ->
        let thisVar = Environment.newVar thisName
        let env = Environment.add (Var(thisName)) (VarRef(thisVar)) env
        match argName with
        | None -> //alias
            let value' = transformExpr env value
            LetRec'(thisVar,value',transformExpr env inValue)
        | Some(x) -> //function definition
            let xVar = Environment.newVar x
            let this = 
                let value' = 
                    let innerEnv = Environment.add (Var(x)) (VarRef(xVar)) env
                    transformExpr innerEnv value
                Fun(xVar,value')
            LetRec'(thisVar,this,transformExpr env inValue)

type TVar = TV of string

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Type =   TVar of TVar 
            | TCon of string
            | TArrow of Type * Type
with
    override this.ToString() =
        let str = match this with
                  | TCon(x) -> x
                  | TVar(TV(var)) -> var
                  | TArrow(f,x) -> sprintf "%s -> %s" (f.ToString()) (x.ToString())
        sprintf "(%s)" str
    member this.AsString = this.ToString()

let intType = TCon "Int"
let boolType = TCon "Bool"

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Scheme = Forall of TVar list * Type
with
    override this.ToString() =
        match this with
        | Forall(vars,t) ->
            let varStrings = List.map (fun (TV(v)) -> "FA." + v) vars
            let varsString = String.concat "" varStrings
            varsString + t.ToString()
    member this.AsString = this.ToString()
    
[<StructuredFormatDisplayAttribute("{AsString}")>]
type TypeEnv = TypeEnv of Map<Var,Scheme>
with
    override this.ToString() =
        match this with
        | TypeEnv(env) ->
            let strings = Seq.map (fun ((Var(v)),sc) -> sprintf "'%s' => %s" v (sc.ToString())) (Map.toSeq env)
            sprintf "%A" strings
    member this.AsString = this.ToString()

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
            | None -> this
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

//m1でm2を上書き
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
        let name = sprintf "%s%d" name !nextIndex
        nextIndex := !nextIndex + 1
        TVar(TV(name))

//replace all free type variables which don't appear in outer environment with ∀
//∀の導入規則
let generalize (env: TypeEnv) (t: Type) =
    Forall(Set.toList (t.freeTypeVariables - env.freeTypeVariables),t)
//instantiate fresh new type variable for each ∀
//∀の除去規則
let instantiate (ts: Scheme) =
    match ts with
    | Forall(vars,t) ->
        let newVars = List.map (fun _ -> newTyVar "a") vars
        let mapping = Map.ofList (List.zip vars newVars)
        t.apply mapping

//bind a name to type
let varBind (var: TVar) (t: Type): Subst =
    match t with
    | TVar(_) -> Map.empty //?
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
            let tv = newTyVar "a"
            //replace outer type variable named {arg} with fresh new variable
            let innerEnv = TypeEnv(Map.add arg (Forall([],tv)) env)
            let subst, t = infer innerEnv body
            subst, TArrow(tv.apply subst,t)
    | Apply'(f,x) -> 
        let tv = newTyVar "a"
        let s1, t1 = infer env f
        let s2, t2 = infer (env.apply s1) x
        let s3 = unify (t1.apply s2) (TArrow(t2,tv))
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

let inferScheme (env: TypeEnv) (expr: Expr') : Scheme =
    let s, t = infer env expr
    generalize (env.apply s) (t.apply s)

type Decl' =   LetDecl' of Var * Expr'
             | LetRecDecl' of Var * Expr'
with
    member this.Name = 
        match this with
        | LetDecl'(n,_) -> n
        | LetRecDecl'(n,_) -> n
    member this.Value = 
        match this with
        | LetDecl'(_,v) -> v
        | LetRecDecl'(_,v) -> v

let rec inferDeclarations (TypeEnv(externs)) (decls: Declaration list) : Map<Var,Expr' * Scheme> = 
    let transformDecl (env: Environment.Environment) (decl: Declaration) : Decl' =
        match decl with
        | LetDecl(name,argument,body) -> 
            match argument with
            | None -> //alias
                let body' = transformExpr env body
                LetDecl'(Var(name),body')
            | Some(x) -> //function definition 
                let xVar = Environment.newVar x
                let body' = 
                    let innerEnv = Environment.add (Var(x)) (VarRef(xVar)) env
                    transformExpr innerEnv body
                let thisValue = Fun(xVar,body')
                LetDecl'(Var(name),thisValue)
        | LetRecDecl(name,argument,body) -> 
            let thisVar = Var(name)
            let thisRef = VarRef(thisVar)
            let innerEnv = Environment.add thisVar thisRef env
            match argument with
            | None -> //alias
                let body' = transformExpr innerEnv body
                LetRecDecl'(thisVar,body')
            | Some(x) -> //function definition
                let xVar = Environment.newVar x
                let body' = 
                    let innerEnv = Environment.add (Var(x)) (VarRef(xVar)) innerEnv
                    transformExpr innerEnv body
                let thisValue = Fun(xVar,body')
                LetRecDecl'(thisVar,body')
    let inferDecl env (decl: Decl'): TypeEnv * Scheme = 
        match decl with
        | LetDecl'(name,this) -> 
            let s1, t1 = infer env this
            let newEnv = env.apply s1
            newEnv,generalize newEnv t1
        | LetRecDecl'(name,value) -> failwith "hoge"
    let impl inferredDecls decl =
        //type environment
        let externTyEnv = Map.map (fun _ (_,scheme) -> scheme) inferredDecls
        //name environment
        let externEnv = Map.map (fun v (_,_) -> VarRef(v)) inferredDecls
        let decl = transformDecl externEnv decl
        let newTyEnv,scheme = inferDecl (TypeEnv(externTyEnv)) decl
        Map.add decl.Name (decl.Value,scheme) inferredDecls
    let externs = Map.map (fun var scheme -> (VarRef(var),scheme)) externs
    List.fold impl externs decls

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
        let id x = x;
        let const x =
            let f y = id x in
            f;
        let succ x = plus x 1;
        let zero = 0;
        let three = 3;
        let main = 
            succ (const (id zero) three);
        """
    printfn "%s" source
    (*match run pexpr source with
    | Success(result,_,_) ->
        printfn "%A" result;
        let result = transformExpr Environment.empty result
        printfn "%A" result;
        let primitiveEnv =
            let plus = (Var("plus")), (Forall([],TArrow(intType,TArrow(intType,intType))))
            let minus = (Var("minus")), (Forall([],TArrow(intType,TArrow(intType,intType))))
            let multiply = (Var("multiply")), (Forall([],TArrow(intType,TArrow(intType,intType))))
            let eq = (Var("eq")), (Forall([],TArrow(intType,TArrow(intType,boolType))))
            let env = Map.ofList [plus;minus;multiply;eq]
            let env = Map.add (Var("undefined")) (let anyType = TV("a") in (Forall([anyType],TVar(anyType)))) env
            TypeEnv(env)
        printfn "%A" (inferScheme primitiveEnv result)
    | Failure(msg,_,_) -> printfn "%s" msg*)
    match run pprogram source with
    | Success(decls,_,_) -> 
        (*let env =
            let env = Map.add (Var("plus")) (Forall([],TArrow(intType,TArrow(intType,intType)))) Map.empty
            TypeEnv(env)
        let result = inferDeclarations env decls
        printfn "%A" result*)
        let decls = AlphaTransform.alphaTransformDecls (Set.ofList ["plus"]) decls
        //printfn "declarations: %A" decls
        let extractedDecls = Closure.transformDecls [Closure.Var("plus")] decls
        printfn "closure transformed declarations:"
        for decl in extractedDecls do
            printfn "  %A" decl
    | Failure(msg,_,_) -> printfn "%s" msg
    0 // return an integer exit code
