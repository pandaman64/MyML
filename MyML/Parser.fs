module Parser

open FParsec
open Common

type Expr =   Literal of int
            | Identifier of string
            | Let of string * string list * Expr * Expr
            | LetRec of string * string list * Expr * Expr
            | Apply of Expr * Expr list
            | If of Expr * Expr * Expr
            | BinOp of Expr * Operator * Expr

type Declaration = LetDecl of string * string list * Expr
                 | LetRecDecl of string * string list * Expr

type MLParser<'a> = Parser<'a,unit>

let pexpr,pexprRef = createParserForwardedToRef<Expr,unit>()

let pliteral:MLParser<Expr> = pint32 .>> spaces |>> Literal

let pidentifierString:MLParser<string> = 
    let palphabet = satisfy isLetter
    let pfollowing = 
        let pred c = isLetter c || isDigit c || isAnyOf "!?" c
        satisfy pred
    let reservedWords = ["if";"then";"else";"in";"let"]
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

let papplyOrValue:MLParser<Expr> = parse{
    let! head,tail = pvalue .>>. (many pvalue)
    match tail with
    | [] -> return head //引数がないときはそのまま返す
    | exprs -> return Apply(head,exprs) //あるときは適用して返す
}

let pbinop (pfactor: MLParser<Expr>) (ops: Map<char,Operator>):MLParser<Expr> = 
    let pop = satisfy ops.ContainsKey
              |>> ops.TryFind
              |>> Option.get
    let pterm = parse{ 
        let! op = pop
        return fun lhs rhs -> BinOp(lhs,op,rhs)
    }
    chainl1 pfactor pterm

let pmultitive:MLParser<Expr> = 
    [ '*',Multiply; '/',Divide ]
    |> Map.ofList
    |> pbinop papplyOrValue 

let padditive:MLParser<Expr> =
    [ '+',Add; '-',Subtract ]
    |> Map.ofList
    |> pbinop pmultitive

pexprRef := spaces >>. choice [
    attempt pletrec;
    attempt plet;
    attempt pif;
    attempt pliteral;
    padditive
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

let pdecls = 
    let pdeclOne = pletrecDecl <|> pletDecl
    spaces >>. many pdeclOne

let pprogram = pdecls
