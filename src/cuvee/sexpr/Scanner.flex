package cuvee.sexpr;

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

digit   = [0-9]
letter  = [a-zA-Z]
extra   = [~!@$%&*_+=<>.?/] | "-" | "^"

num     = [1-9]{digit}* | 0
dec     = {num} "\." 0* {num}
hex     = "#x" [0-9a-fA-F]+
bin     = "#b" [01]+

symbol0 = {letter} | {extra}
symbol1 = {letter} | {extra} | {digit}
symbol  = {symbol0} {symbol1}*

quoted  = \| ~ \|

kw      = ":" {symbol}

%%

<YYINITIAL> {

{ws}+ {}
";" .* {nl} {}

"("         { return Syntax.lp();   }
")"         { return Syntax.rp();   }

// strings, where a doubled "" inside a string stands for " (SMT-LIB 2.6)
\" ([^\"] | \"\")* \"
            { return Syntax.value("str", yytext(+1,-1).replace("\"\"", "\"")); }

{dec}       { return Syntax.value("dec", yytext()); }
{num}       { return Syntax.value("num", yytext()); }
{hex}       { return Syntax.value("hex", yytext(+2,0)); }
{bin}       { return Syntax.value("bin", yytext(+2,0)); }

{symbol}    { return Syntax.value("id", yytext()); }
{quoted}    { return Syntax.value("id", yytext(+1,-1)); }
{kw}        { return Syntax.value("kw", yytext(+1,0));  }

[^]         { Syntax.error("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
