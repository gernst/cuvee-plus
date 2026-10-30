package cuvee.boogie;

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

num  = [0-9]+
dec  = {num} "." [0-9]+

kw  = "type" | "data" | "and" | "const" | "function" | "axiom" | "lemma" | "var" | "procedure"
    | "returns" | "requires" | "ensures" | "modifies" | "invariant" | "decreases"
    | "if" | "then" | "else" | "while" | "break" | "continue" | "return"
    | "assert" | "assume" | "havoc" | "call" | "forall" | "exists" | "lambda"
    | "trace" | "map" | "all" | "for" | "do" | "yield" | "check" | "case" | "annotate" | "verify"
    | "logic" | "option" | "info" | "witness" | "labels" | "model" | "exit" | "push" | "pop" | "reset"
    | "(" | ")" | "[" | "]" | "::" | [;,:{}|] | ":=" | "=" | "=>" | "<" | ">" | "*" | "⌊" | "⌋"

// identifiers as in Boogie, together with the subscripts of indexed names
idchar = [a-zA-Z'~#$\^_.?`\\⁰-⁹₀-₉]

// the opening of an attribute with its name, which may contain hyphens, e.g. {:check-true of SV-LIB
attr = "{:" {idchar} ({idchar} | [0-9] | "-")*

sym = {idchar} ({idchar} | [0-9])*
    | [+\-/] | "&&" | "||" | "==>" | "<==>" | "!"
    | "==" | "!=" | "<=" | ">="

%%

<YYINITIAL> {

{ws}+ {}
"//" .* {nl} {}
"/*" ~"*/" {}

{attr}      { return Syntax.apply("attr", yytext(2,0)); }
{kw}        { return Syntax.apply(yytext()); }
\" ([^\"\\] | \\.)* \"     { return Syntax.apply("str", yytext(+1,-1)); }
{dec}       { return Syntax.apply("dec", yytext()); }
{num}       { return Syntax.apply("num", yytext()); }
{sym}       { return Syntax.apply("sym", yytext()); }
"`" [^`]* "`"  { return Syntax.apply("sym", yytext(+1,-1)); }

[^]         { throw new RuntimeException("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
