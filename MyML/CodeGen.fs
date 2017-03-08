module CodeGen

open Common

type Label = { name: string; id: int list }
let newLabel = 
    let mutable counter = 0
    let func name = 
        counter <- counter + 1
        { name = name; id = [counter] }
    func
let mergeLabel (lhs: Label) (rhs: Label) =
    { name = lhs.name + " " + rhs.name; id = List.append lhs.id rhs.id } 

type OpCode =   Nop
              | Add
              | Subtract
              | Multiply
              | Divide
              | LdLoc of Var
              | StLoc of Var
              | Push of int
              | Pop
              | BTrue of Label
              | Jmp of Label
              | Call
              | Ret
              | Label of Label

type Statement = { opcode: OpCode; label: Label option }
let statement opcode = { opcode = opcode; label = None}

type Assembly = Statement list

type Declaration = Label

let rec generateExpr (expr: TypeInference.TypedExpr) (locals: Set<Var>) (externs: Map<Var,Declaration>)
    (label: Label option) (statements: Assembly): Label option * Assembly = 
    match expr.value with
    | TypeInference.Literal(x) -> None,statement (Push(x)) :: statements
    | TypeInference.BinOp(lhs,op,rhs) ->
        let label,statements = generateExpr lhs locals externs label statements 
        let label,statements = generateExpr rhs locals externs label statements 
        None,match op with
             | Operator.Add -> Add
             | Operator.Subtract -> Subtract
             | Operator.Multiply -> Multiply
             | Operator.Divide -> Divide
             |> fun op -> { opcode = op; label = label } :: statements
    | TypeInference.Apply(f,xs) ->
        let label,statements = (label,statements)
                               |> List.foldBack (fun x (label,statements) -> generateExpr x locals externs label statements) xs
        let label,statements = generateExpr f locals externs label statements
        None,{ opcode = Call; label = label } :: statements
    | TypeInference.Alias(name,value,body) -> 
        let label,statements = generateExpr value locals externs label statements
        let statments = statement (StLoc(name)) :: statements
        generateExpr body (Set.add name locals) externs label statements
    | TypeInference.AliasRec(name,value,body) -> 
        let label,statements = generateExpr value locals externs label statements
        let statments = statement (StLoc(name)) :: statements
        generateExpr body (Set.add name locals) externs label statements
    | TypeInference.ApplyClosure(closure,application) ->
        failwith "no idea"
    | TypeInference.If(cond,ifTrue,ifFalse) ->
        // generate like below codes
        //
        // 'cond'
        // BTrue IFFALSE
        // 'ifTrue'
        // Jmp IFEND
        // IFFALSE: 'ifFalse'
        // IFEND:
        let label,statements = generateExpr cond locals externs label statements
        let falseLabel = newLabel "IFFALSE"
        let statements = { opcode = BTrue(falseLabel); label = label } :: statements
        let label,statements = generateExpr ifTrue locals externs None statements
        let endLabel = newLabel "IFEND"
        let statements = { opcode = Jmp(endLabel); label = label } :: statements
        let label,statements = generateExpr ifFalse locals externs (Some(falseLabel)) statements
        match label with
        | None -> endLabel
        | Some(label) -> mergeLabel label endLabel
        |> Some,statements
    | TypeInference.ExternRef(name) ->
        if Set.contains name locals
        then
            None,{ opcode = LdLoc(name); label = label } :: statements
        else 
            match externs.TryFind name with
            | Some(decl) -> None,{ opcode = Label(decl); label = label } :: statements
            | None -> failwithf "variable %A not found in %A, %A" name locals externs
        

let generateDecl decl = failwith "bbb"

let generateDecls decls = failwith "ccc"