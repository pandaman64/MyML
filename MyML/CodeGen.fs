module CodeGen

open Common

module TI = TypeInference
let rec isVariadic (type_: TI.Type): bool =
    match type_ with
    | TI.TVariable(_) -> true
    | TI.TConstructor(_) -> false
    | TI.TArrow(f,x) ->
        isVariadic f || isVariadic x
    | TI.TClosure(t,applications) ->
        isVariadic t || applications
                        |> Map.exists (fun _ t -> isVariadic t)

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Label = { name: string; id: int list }
with
    member this.AsString = 
        sprintf "%s" this.name
let newLabel = 
    let mutable counter = 0
    let func name = 
        counter <- counter + 1
        { name = name; id = [counter] }
    func
let mergeLabel (lhs: Label) (rhs: Label) =
    { name = lhs.name + " " + rhs.name; id = List.append lhs.id rhs.id } 

[<StructuredFormatDisplayAttribute("{AsString}")>]
type Slot = { id: int }
with
    member this.AsString = sprintf "`%d" this.id
let newSlot: unit -> Slot = 
    let mutable counter = 0
    let func _ =
        counter <- counter + 1
        { id = counter }
    func

[<StructuredFormatDisplayAttribute("{AsString}")>]
type OpCode =   Nop
              | Exit
              | Add
              | Subtract
              | Multiply
              | Divide
              | LdLoc of Var
              | StLoc of Var
              | LdArg of Var
              | StArg of Var
              | Push of int
              | Pop
              | BTrue of Label
              | Jmp of Label
              | Call
              | Ret
              | Label of Label
              | Ld of Slot
              | St of Slot
with
    member this.AsString =
        match this with
        | Nop -> "NOP"
        | Exit -> "EXIT"
        | Add -> "ADD" 
        | Subtract -> "SUB" 
        | Multiply -> "MUL"
        | Divide -> "DIV"
        | Push(x) -> sprintf "PUSH  %d" x
        | Pop -> "POP"
        | Call -> "CALL"
        | Ret -> "RET"
        | LdLoc(name) -> sprintf "LDLOC  %A" name
        | StLoc(name) -> sprintf "STLOC  %A" name
        | LdArg(name) -> sprintf "LDARG  %A" name 
        | StArg(name) -> sprintf "STARG  %A" name
        | BTrue(label) -> sprintf "BTRUE  %A" label
        | Jmp(label) -> sprintf "JMP  %A" label
        | Label(label) -> sprintf "LABEL  %A" label
        | Ld(slot) -> sprintf "LD  %A" slot
        | St(slot) -> sprintf "ST  %A" slot

type Statement = { opcode: OpCode; label: Label option }
with
    member this.AsString = 
        match this.label with
        | None -> sprintf "%A" this.opcode
        | Some(label) -> sprintf "%s:  %A" label.name this.opcode
let statement opcode = { opcode = opcode; label = None}

type Assembly = Statement list
let assemblyString (asm: Assembly):string =
    asm
    |> Seq.map (fun statement -> statement.AsString)
    |> String.concat "\n"

type DeclarationBuilder = { assembly: Assembly; nextLabel: Label option }
with
    member this.Emit next opcode = 
        { 
            assembly = { opcode = opcode; label = this.nextLabel } :: this.assembly ; 
            nextLabel = next
        }
    member this.MarkLabel label = 
        match this.nextLabel with
        | None -> { assembly = this.assembly; nextLabel = Some(label) }
        | Some(label') -> { assembly = this.assembly; nextLabel = Some(mergeLabel label label') }

type AssemblyInformation() =
    let mutable declarations: Map<Var,TI.Declaration * Map<TI.Type,Label * Assembly>> = Map.empty
    let mutable declBuilders: DeclarationBuilder list = []
    let mutable slots: Slot list = []

    member this.Emit next opcode =
        match declBuilders with
        | [] -> failwith "not in declaration scope"
        | head :: tail -> declBuilders <- head.Emit next opcode :: tail
    member this.MarkLabel label =
        match declBuilders with
        | [] -> failwith "not in declaration scope"
        | head :: tail -> declBuilders <- head.MarkLabel label :: tail
    member this.Push =
        declBuilders <- { assembly = []; nextLabel = None } :: declBuilders
    member this.Pop = 
        match declBuilders with
        | [] -> failwith "cannot pop from empty stack"
        | head :: tail -> 
            declBuilders <- tail
            List.rev head.assembly
    member this.instantiate name type_ = 
        match declarations.TryFind name with
        | None -> failwithf "declaration %A not found in %A" name declarations
        | Some(decl,instances) ->
            match instances.TryFind type_ with
            | Some(label,_) -> label
            | None -> 
                if isVariadic type_ then failwith "need type passing to generate variadic functions. implement later"
                else
                    match decl with
                    | TI.FreeValue(name,value) -> 
                        let slot = newSlot ()
                        let entryPoint = newLabel (sprintf "%A" name)
                        let expr:TI.TypedExpr = { value = value.value; type_ = type_ }
                        // generate constructor
                        this.generateExpr expr Set.empty Set.empty
                        this.Emit None (St(slot))

                        // generate getter function
                        this.Push
                        this.MarkLabel entryPoint
                        this.Emit None (Ld(slot))
                        this.Emit None Ret
                        let assembly = this.Pop
                        let instances = Map.add type_ (entryPoint,assembly) instances
                        declarations <- Map.add name (decl,instances) declarations
                        entryPoint
                    | TI.FreeFunction(name,value) | TI.FreeRecFunction(name,value) ->
                        let subst = TI.unify (TI.instantiate value.type_) (type_)
                        let value = value.value.Apply subst
                        let arguments = Set.ofList value.argument
                        let locals = Set.empty
                        let entryPoint = 
                            let substString = subst
                                              |> Map.toSeq
                                              |> Seq.map snd
                                              |> Seq.map (fun x -> sprintf "%A" x)
                                              |> String.concat "_"
                            let labelName = if subst.IsEmpty 
                                            then sprintf "%A" name 
                                            else sprintf "%A_%A" name substString
                            newLabel labelName
                        
                        // register a stub for recursive call
                        let instances = Map.add type_ (entryPoint,[]) instances
                        declarations <- Map.add name (decl,instances) declarations

                        this.Push
                        this.MarkLabel entryPoint
                        for arg in value.argument do
                            this.Emit None (StArg(arg))
                        this.generateExpr value.body arguments locals
                        this.Emit None Ret
                        let assembly = this.Pop

                        // re-register the content
                        let instances = Map.add type_ (entryPoint,assembly) instances
                        declarations <- Map.add name (decl,instances) declarations
                        entryPoint
                    | _ -> failwith "no idea"
                        
        member info.generateExpr (expr: TI.TypedExpr) (arguments: Set<Var>) (locals: Set<Var>): unit = 
            match expr.value with
            | TI.Literal(x) -> info.Emit None (Push(x))
            | TI.BinOp(lhs,op,rhs) ->
                info.generateExpr lhs arguments locals 
                info.generateExpr rhs arguments locals 
                let op = match op with
                            | Operator.Add -> Add
                            | Operator.Subtract -> Subtract
                            | Operator.Multiply -> Multiply
                            | Operator.Divide -> Divide
                info.Emit None op
            | TI.Apply(f,xs) ->
                for x in List.rev xs do
                    info.generateExpr x arguments locals
                info.generateExpr f arguments locals
                match expr.type_ with
                | TI.TArrow(_,_) -> ignore "partial application"
                | TI.TClosure(TI.TArrow(_,_),_) -> ignore "partial application"
                | _ -> info.Emit None Call
            | TI.Alias(name,value,body) ->
                info.generateExpr value arguments locals
                info.Emit None (StLoc(name))
                info.generateExpr body arguments (Set.add name locals)
            | TI.AliasRec(name,value,body) ->
                info.generateExpr value arguments (Set.add name locals)
                info.Emit None (StLoc(name))
                info.generateExpr body arguments (Set.add name locals)
            | TI.ApplyClosure(closure,application) ->
                failwith "no idea"
            | TI.If(cond,ifTrue,ifFalse) ->
                // generate like below codes
                //
                // 'cond'
                // BTrue IFFALSE
                // 'ifTrue'
                // Jmp IFEND
                // IFFALSE: 'ifFalse'
                // IFEND:
                info.generateExpr cond arguments locals
                let falseLabel = newLabel "IFFALSE"
                info.Emit None (BTrue(falseLabel)) 
                info.generateExpr ifTrue arguments locals
                let endLabel = newLabel "IFEND"
                info.Emit None (Jmp(endLabel))
                info.MarkLabel falseLabel
                info.generateExpr ifFalse arguments locals
                info.MarkLabel endLabel
            | TI.ExternRef(name) ->
                if Set.contains name arguments
                then
                    info.Emit None (LdArg(name))
                else if Set.contains name locals
                then
                    info.Emit None (LdLoc(name))
                else 
                    info.Emit None (Label(info.instantiate name expr.type_))

        member this.generateDecls (decls: TI.Declaration list):Assembly = 
            this.Push
            for decl in decls do
                declarations <- Map.add decl.Name (decl,Map.empty) declarations
                match decl with
                | TI.FreeValue(name,value) (*when not (isVariadic (TI.instantiate value.type_))*) -> 
                    ignore (this.instantiate name (TI.instantiate value.type_))
                | _ -> ignore "do nothing"
            this.Emit None Exit
            let main = this.Pop
            let functions = declarations
                            |> Map.toSeq
                            |> Seq.map (snd >> snd)
                            |> Seq.map (Map.toSeq >> Seq.map (snd >> snd))
                            |> Seq.concat
                            |> Seq.toList
            List.concat (main :: functions)