﻿open FParsec
open Common

[<EntryPoint>]
let main argv = 
    let source = """
        type record = { field: Int; function: Int -> Int; };
        let succ x = x + 1;
        let sum min max =
            let rec loop x =
                if x = max then max
                else x + loop (x + 1) in
            loop min;
        let a x =
            let rec inf y = inf y in
            inf;
        let main = 
            let x = { field = sum 0 10; function = succ; } in
            x.field;
        """
    printfn "%s" source
    match run Parser.pprogram source with
    | Success(decls,_,_) -> 
        (*let env =
            let env = Map.add (Var("plus")) (Forall([],TArrow(intType,TArrow(intType,intType)))) Map.empty
            TypeEnv(env)
        let result = inferDeclarations env decls
        printfn "%A" result*)
        let decls = AlphaTransform.alphaTransformDecls (Set.ofList []) decls
        //printfn "declarations: %A" decls
        let extractedDecls = Closure.transformDecls [] decls
        printfn "closure transformed declarations:"
        for decl in extractedDecls do
            printfn "  %A" decl
        let typeEnv = 
            [
                Var("+"),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.intType));
                Var("-"),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.intType));
                Var("*"),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.intType));
                Var("/"),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.intType));
                Var("="),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.boolType));
                Var("!="),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.boolType));
                Var("<"),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.boolType));
                Var("<="),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.boolType));
                Var(">"),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.boolType));
                Var(">="),TypeInference.TArrow(TypeInference.intType,TypeInference.TArrow(TypeInference.intType,TypeInference.boolType));
            ]
            |> Map.ofSeq
            |> Map.map (fun _ t -> TypeInference.Scheme.fromType t)
            |> TypeInference.TypeEnv
        let typeNameEnv = 
            [
                Var("Int"),TypeInference.intType;
                Var("Bool"),TypeInference.boolType;
            ]
            |> Map.ofSeq
        let env:TypeInference.Environment = { typeEnv = typeEnv; typeNameEnv = typeNameEnv; recordEnv = Map.empty }
        let inferredDecls' = TypeInference.inferDecls' env extractedDecls
        printfn "type inferred declarations [NEW! Monadic Version]:"
        for decl in inferredDecls' do
            printfn "  %A" decl
        //let info = new CodeGen.AssemblyInformation()
        //let assembly = info.generateDecls inferredDecls
        //printfn "%s" (CodeGen.assemblyString assembly)
    | Failure(msg,_,_) -> printfn "%s" msg
    0 // return an integer exit code
