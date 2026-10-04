package cuvee.dafny;

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

%{
    public final String yytext(int start, int end) {
        int length = zzMarkedPos-zzStartRead;
        return new String( zzBuffer, zzStartRead + start, length - start + end );
    }
%}

nl = \r|\n|\r\n
ws = {nl} | [ \t\f]

num  = [1-9][0-9]* | 0
dec  = {num} "." [0-9]+

kw  = "function" | "predicate" | "axiom" | "const" | "datatype" | "type" | "method"
    | "returns" | "requires" | "ensures" | "modifies" | "invariant" | "decreases"
    | "while" | "if" | "then" | "else" | "assert" | "assume" | "var"
    | "break" | "continue" | "return"
    | "(" | ")" | "[" | "]" | "::" | [;,:{}] | ":=" | "=" | "|" | "." | ".."

sym = [a-zA-Z_][a-zA-Z0-9⁰-⁹₀-₉_~#$?]*
    | [+\-*/%] | "&&" | "||" | "==>" | "<==>" | "!"
    | "==" | "!=" | "<=" | "<" | ">" | ">=" | "'"

%%

<YYINITIAL> {

{ws}+ {}
"//" .* {nl} {}

{kw}        { return Syntax.apply(yytext()); }
\" ~ \"     { return Syntax.apply("str", yytext(+1,-1)); }
{dec}       { return Syntax.apply("dec", yytext()); }
{num}       { return Syntax.apply("num", yytext()); }
{sym}       { return Syntax.apply("sym", yytext()); }

[^]         { throw new RuntimeException("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
