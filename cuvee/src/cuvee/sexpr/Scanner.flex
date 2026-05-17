package cuvee.sexpr;

%%

%public
%class Scanner
%function next
%type cuvee.util.Tok

%eofval{
    return Grammar.eof();
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
hex     = "0x" [0-9a-fA-F]+
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

"("         { return Grammar.lp();   }
")"         { return Grammar.rp();   }

\" ~ \"
            { return Grammar.str(yytext(+1,-1)); }

{dec}       { return Grammar.dec(yytext()); }
{num}       { return Grammar.num(yytext()); }
{hex}       { return Grammar.hex(yytext(+2,0)); }
{bin}       { return Grammar.bin(yytext(+2,0)); }

{symbol}    { return Grammar.id(yytext()); }
{quoted}    { return Grammar.id(yytext(+1,-1)); }
{kw}        { return Grammar.kw(yytext(+1,0));  }

[^]         { throw new RuntimeException("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
