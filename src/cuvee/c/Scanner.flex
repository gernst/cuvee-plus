package cuvee.c;

%%

%public
%class Scanner
%implements cuvee.pipe.Scanner
%function next
%type easyparse.Token

%eofval{
    return easyparse.Token.eof();
%eofval}

%line
%column

nl = \r|\n|\r\n
ws = {nl} | [ \t\f]

num  = [0-9]+

// type qualifiers and storage classes are ignored by the grammar
kw  = "int" | "long" | "short" | "char" | "unsigned" | "signed" | "_Bool" | "bool" | "void"
    | "const" | "static" | "extern" | "volatile"
    | "if" | "else" | "while" | "do" | "for" | "break" | "continue" | "return"
    | "(" | ")" | "[" | "]" | [;,{}?:]
    | "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "++" | "--"

id  = [a-zA-Z_] [a-zA-Z0-9_]*
sym = {id}
    | [+\-*/%!<>] | "&&" | "||" | "==" | "!=" | "<=" | ">="

%%

<YYINITIAL> {

{ws}+ {}
"//" .* {nl} {}
"/*" ~"*/" {}
// preprocessor directives are skipped
"#" .* {nl} {}

{kw}        { return Syntax.apply(yytext()); }
{num}       { return Syntax.apply("num", yytext()); }
{sym}       { return Syntax.apply("sym", yytext()); }

[^]         { throw new RuntimeException("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
