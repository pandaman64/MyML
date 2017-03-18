module Parser

open FParsec
open Common

type Expr =   IntegerLiteral of int
            | Identifier of string
            | Let of string * string list * Expr * Expr
            | LetRec of string * string list * Expr * Expr
            | Apply of Expr * Expr list
            | If of Expr * Expr * Expr
            | BinOp of Expr * Operator * Expr
            | RecordLiteral of Map<string,Expr>
            | RecordAccess of Expr * string

type TypeDecl =   Record of Map<string,string>
                | TyAlias of string

type Declaration = LetDecl of string * string list * Expr
                 | LetRecDecl of string * string list * Expr
                 | TypeDecl of string * TypeDecl

type MLParser<'a> = Parser<'a,unit>

let pexpr,pexprRef = createParserForwardedToRef<Expr,unit>()

let pliteral:MLParser<Expr> = pint32 .>> spaces |>> IntegerLiteral

let pidentifierString:MLParser<string> = 
    let palphabet = satisfy isLetter
    let pfollowing = 
        let pred c = isLetter c || isDigit c || isAnyOf "!?" c
        satisfy pred
    let reservedWords = ["if";"then";"else";"in";"let";"type"]
    let parser = parse{
        let! id = many1Chars2 palphabet pfollowing .>> spaces
        if List.contains id reservedWords then 
            do! fail "reserved word"
            return id
        else 
            return id 
    }
    attempt parser

let pidentifier:MLParser<Expr> = pidentifierString |>> Identifier

let plet:MLParser<Expr> = parse{
    let! name = attempt (pstring "let" >>. spaces >>. pidentifierString)
    let! parameters = many pidentifierString
    do! pchar '=' >>. spaces
    let! bind = pexpr
    do! pstring "in" >>. spaces
    let! body = pexpr
    return Let(name,parameters,bind,body)
}

let pletrec:MLParser<Expr> = parse{
    let! name = attempt (pstring "let" >>. spaces >>. pstring "rec" >>. spaces >>. pidentifierString)
    let! parameters = many pidentifierString
    do! pchar '=' >>. spaces
    let! bind = pexpr
    do! pstring "in" >>. spaces
    let! body = pexpr
    return LetRec(name,parameters,bind,body)
}

let pif:MLParser<Expr> = parse{
    do! attempt (pstring "if" >>. spaces)
    let! condition = pexpr
    do! pstring "then" >>. spaces
    let! thenExpr = pexpr
    do! pstring "else" >>. spaces
    let! elseExpr = pexpr
    return If(condition,thenExpr,elseExpr)
}

let pprimitive:MLParser<Expr> = spaces >>. choice [
                                    attempt pletrec;
                                    attempt plet;
                                    attempt pif;
                                    attempt pliteral;
                                    pidentifier
                                ] .>> spaces

let pvalue:MLParser<Expr> = 
    let braced = between (pchar '(' >>. spaces) (pchar ')' >>. spaces) pexpr
    braced <|> pprimitive

let precordAccess: MLParser<Expr> = parse{
    let! obj = pvalue
    let! dot = opt (pchar '.' >>. spaces)
    match dot with
    | None -> return obj
    | Some(_) -> 
        let! field = pidentifierString
        return RecordAccess(obj,field)
}

let papply:MLParser<Expr> = parse{
    let! head,tail = precordAccess .>>. (many precordAccess)
    match tail with
    | [] -> return head //引数がないときはそのまま返す
    | exprs -> return Apply(head,exprs) //あるときは適用して返す
}

let pbinop (pfactor: MLParser<Expr>) (ops: (string * Operator) list):MLParser<Expr> = 
    let pop = ops
              |> List.map (fun (op,value) -> attempt (pstring op >>% value))
              |> choice
    let pterm = parse{ 
        let! op = pop
        return fun lhs rhs -> BinOp(lhs,op,rhs)
    }
    chainl1 pfactor pterm

let pmultitive:MLParser<Expr> = 
    [ "*",Multiply; "/",Divide ]
    |> pbinop papply 

let padditive:MLParser<Expr> =
    [ "+",Add; "-",Subtract ]
    |> pbinop pmultitive

let prelational: MLParser<Expr> =
    [
        "=",Equal;
        "!=",NotEqual;
        "<=",LessThanOrEq;
        "<",LessThan;
        ">=",GreaterThanOrEq;
        ">",GreaterThan;
    ]
    |> pbinop padditive

let precordLiteral: MLParser<Expr> = parse{
    do! pchar '{' >>. spaces
    let pfield = pidentifierString .>>. (pchar '=' >>. spaces >>. pexpr)
    let! content = sepBy pfield (pchar '=' >>. spaces) 
    do! pchar '}' >>. spaces
    return RecordLiteral(Map.ofList content)
}

pexprRef := spaces >>. choice [
    attempt pletrec;
    attempt plet;
    attempt pif;
    attempt pliteral;
    attempt precordLiteral;
    prelational
] .>> spaces

let pletDecl:MLParser<Declaration> = parse{
    let! name = attempt (pstring "let" >>. spaces >>. pidentifierString)
    let! parameters = many pidentifierString
    do! pchar '=' >>. spaces
    let! bind = pexpr
    do! pchar ';' >>. spaces
    return LetDecl(name,parameters,bind)
}

let pletrecDecl:MLParser<Declaration> = parse{
    let! name = attempt (pstring "let" >>. spaces >>. pstring "rec" >>. spaces >>. pidentifierString)
    let! parameters = many pidentifierString
    do! pchar '=' >>. spaces
    let! bind = pexpr
    do! pchar ';' >>. spaces
    return LetRecDecl(name,parameters,bind)
}

let precordDecl:MLParser<TypeDecl> = parse{
    do! pchar '{' >>. spaces
    let! content = 
        let pfield = pidentifierString .>>. (pchar ':' >>. spaces >>. pidentifierString)
        sepEndBy1 pfield (pchar ';' >>. spaces)
        |>> Map.ofList
    do! pchar '}' >>. spaces
    return Record(content)
}

let ptypeDecl:MLParser<Declaration> = parse{
    do! pstring "type" >>. spaces
    let! name = pidentifierString
    do! pchar '=' >>. spaces
    let! decl = choice [
                    precordDecl;
                    pidentifierString |>> TyAlias
                ]
    do! pchar ';' >>. spaces
    return TypeDecl(name,decl)
}

let pdecls = 
    let pdeclOne = choice [
                          pletrecDecl;
                          pletDecl;
                          ptypeDecl
                          ] 
    spaces >>. many pdeclOne

let pprogram = pdecls
