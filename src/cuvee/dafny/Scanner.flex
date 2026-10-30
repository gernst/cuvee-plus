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

kw  = "function" | "predicate" | "axiom" | "lemma" | "goal" | "const" | "datatype" | "type" | "method" | "static"
    | "returns" | "requires" | "ensures" | "modifies" | "invariant" | "decreases"
    | "while" | "if" | "then" | "else" | "assert" | "assume" | "var"
    | "forall" | "exists" | "break" | "continue" | "return" | "parallel" | "as" | "assumes" | "commits" | "ode" | "check" | "map" | "multiset"
    | "trace" | "maps" | "invs" | "match" | "case" | "for" | "do" | "yield" | "fuse" | "include" | "???"
    | "annotate" | "verify" | "logic" | "option" | "info" | "witness" | "labels" | "model" | "exit" | "push" | "pop" | "reset"
    | "(" | ")" | "[" | "]" | "::" | [;,:{}] | ":=" | "=" | "=>" | "->" | "==" | "<" | ">" | "*" | "'" | "|" | "." | ".." | "⌊" | "⌋"

// the opening of an annotation with its name, which may contain hyphens, e.g. {:check-true of SV-LIB
attr = "{:" [a-zA-Zω_] [a-zA-Z0-9_\-]*

sym = [a-zA-Zω_][a-zA-Z0-9⁰-⁹₀-₉_~#$?]*
    | "until+" | "unless+" | "release+"
    | [+\-/%] | "&" | "^" | "&&" | "||" | "==>" | "<==>" | "!"
    | "!=" | "<=" | ">="

%%

<YYINITIAL> {

{ws}+ {}
"//" .* {nl} {}

{attr}      { return Syntax.apply("attr", yytext(2,0)); }
{kw}        { return Syntax.apply(yytext()); }
\" ([^\"\\] | \\.)* \"     { return Syntax.apply("str", yytext(+1,-1)); }
{dec}       { return Syntax.apply("dec", yytext()); }
{num}       { return Syntax.apply("num", yytext()); }
"!in" / [^a-zA-Z0-9_]  { return Syntax.apply("sym", yytext()); }
{sym}       { return Syntax.apply("sym", yytext()); }
"`" [^`]* "`"  { return Syntax.apply("sym", yytext(+1,-1)); }

[^]         { throw new RuntimeException("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
