module Parser

open FParsec

type Expr =   Literal of int
            | Identifier of string
            | Let of string * string option * Expr * Expr
            | LetRec of string * string option * Expr * Expr
            | Apply of Expr * Expr list
            | If of Expr * Expr * Expr

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
    //let! parameters = many pidentifierString
    let! parameters = opt pidentifierString
    do! pchar '=' >>. spaces
    let! bind = pexpr
    do! pstring "in" >>. spaces
    let! body = pexpr
    return Let(name,parameters,bind,body)
}

let pletrec:MLParser<Expr> = parse{
    let! name = attempt (pstring "let" >>. spaces >>. pstring "rec" >>. spaces >>. pidentifierString)
    //let! parameters = many pidentifierString
    let! parameters = opt pidentifierString
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

let papply:MLParser<Expr> = pvalue .>>. (many pvalue) |>> Apply

pexprRef := spaces >>. choice [
    attempt pletrec;
    attempt plet;
    attempt pif;
    attempt pliteral;
    attempt papply;
    pidentifier
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
    spaces >>. many (attempt pdeclOne)

let pprogram = pdecls .>>. pexpr
