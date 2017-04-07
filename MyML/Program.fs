open FParsec
open Common

module ETI = EarlyTypeInference
module TS = ETI.TypeSystem

[<EntryPoint>]
let main argv = 
    let source = """
        let id x = x;
        let const x y = x;
        let main = const 0 id;
        """
    printfn "%s" source
    match run Parser.pprogram source with
    | Success(decls,_,_) -> 
        printfn "decls = %A" decls
        let decls = AlphaTransform.alphaTransformDecls (Set.ofList []) decls
        printfn "alpha transformed decls = %A" decls
        let environment = {
            ETI.TypeSystem.variables = 
                ETI.TypeSystem.Variables(
                    [
                        Var("+"),{ TS.bindings = Set.empty; ETI.TypeSystem.type_ = TS.TArrow(TS.intType,TS.TArrow(TS.intType,TS.intType)) };
                        Var("-"),{ TS.bindings = Set.empty; ETI.TypeSystem.type_ = TS.TArrow(TS.intType,TS.TArrow(TS.intType,TS.intType)) };
                        Var("*"),{ TS.bindings = Set.empty; ETI.TypeSystem.type_ = TS.TArrow(TS.intType,TS.TArrow(TS.intType,TS.intType)) };
                        Var("/"),{ TS.bindings = Set.empty; ETI.TypeSystem.type_ = TS.TArrow(TS.intType,TS.TArrow(TS.intType,TS.intType)) };
                        Var("="),{ TS.bindings = Set.empty; ETI.TypeSystem.type_ = TS.TArrow(TS.intType,TS.TArrow(TS.intType,TS.boolType)) };
                    ]
                    |> Map.ofList
                );
            ETI.TypeSystem.recordFields = Map.empty;
            ETI.TypeSystem.typeAliases = Map.empty;
        }
        let decls = ETI.inferDecls environment decls
        for decl in decls do
            printfn "%A" decl
    | Failure(msg,_,_) -> printfn "%s" msg
    0 // return an integer exit code
