open FParsec
open Common

[<EntryPoint>]
let main argv = 
    let source = """
        let succ x = x + 1;
        let main = succ 0;
        """
    printfn "%s" source
    match run Parser.pprogram source with
    | Success(decls,_,_) -> 
        (*let env =
            let env = Map.add (Var("plus")) (Forall([],TArrow(intType,TArrow(intType,intType)))) Map.empty
            TypeEnv(env)
        let result = inferDeclarations env decls
        printfn "%A" result*)
        let decls = AlphaTransform.alphaTransformDecls (Set.ofList ["plus"; "eq"; "minus"]) decls
        //printfn "declarations: %A" decls
        let extractedDecls = Closure.transformDecls [Var("plus"); Var("eq"); Var("eq")] decls
        printfn "closure transformed declarations:"
        for decl in extractedDecls do
            printfn "  %A" decl
        let typeEnv = 
            [
                Var("plus"),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.intType));
                Var("minus"),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.intType));
                Var("eq"),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.boolType));
                Var("+"),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.intType))
            ]
            |> Map.ofSeq
            |> Map.map (fun _ t -> TypeInference.Scheme.fromType t)
            |> TypeInference.TypeEnv
        let inferredDecls = TypeInference.inferDecls typeEnv extractedDecls
        printfn "type inferred declarations:"
        for decl in inferredDecls do
            printfn "  %A" decl
        let info = new CodeGen.AssemblyInformation()
        let assembly = info.generateDecls inferredDecls
        printfn "%s" (CodeGen.assemblyString assembly)
    | Failure(msg,_,_) -> printfn "%s" msg
    0 // return an integer exit code
