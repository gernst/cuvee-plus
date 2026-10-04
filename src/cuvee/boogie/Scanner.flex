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

kw  = "type" | "const" | "function" | "axiom" | "var" | "procedure"
    | "returns" | "requires" | "ensures" | "modifies" | "invariant"
    | "if" | "then" | "else" | "while" | "break" | "return"
    | "assert" | "assume" | "havoc" | "call" | "forall" | "exists"
    | "(" | ")" | "[" | "]" | "::" | [;,:{}] | "{:" | ":=" | "="

// identifiers as in Boogie, together with the subscripts of indexed names
idchar = [a-zA-Z'~#$\^_.?`\\⁰-⁹₀-₉]
sym = {idchar} ({idchar} | [0-9])*
    | [+\-*] | "&&" | "||" | "==>" | "<==>" | "!"
    | "==" | "!=" | "<=" | "<" | ">" | ">="

%%

<YYINITIAL> {

{ws}+ {}
"//" .* {nl} {}
"/*" ~"*/" {}

{kw}        { return Syntax.apply(yytext()); }
\" ~ \"     { return Syntax.apply("str", yytext(+1,-1)); }
{num}       { return Syntax.apply("num", yytext()); }
{sym}       { return Syntax.apply("sym", yytext()); }

[^]         { throw new RuntimeException("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
