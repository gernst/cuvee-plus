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

// type qualifiers and storage classes are ignored by the grammar, as are attributes of GCC
kw  = "int" | "long" | "short" | "char" | "unsigned" | "signed" | "_Bool" | "bool" | "void"
    | "const" | "static" | "extern" | "volatile" | "inline" | "restrict" | "__attribute__"
    | "if" | "else" | "while" | "do" | "for" | "break" | "continue" | "return"
    | "(" | ")" | "[" | "]" | [;,{}?:]
    | "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "++" | "--"

// string literals, which occur in the harness of SV-COMP, e.g. as arguments of __assert_fail
str = \" ([^\"\\\n] | \\.)* \"

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

// the spellings of GCC in preprocessed files (.i)
"__extension__" {}
"__const"       { return Syntax.apply("const"); }
"__inline" | "__inline__"     { return Syntax.apply("inline"); }
"__restrict" | "__restrict__" { return Syntax.apply("restrict"); }

{kw}        { return Syntax.apply(yytext()); }
{str}       { return Syntax.apply("str", yytext()); }
{num}       { return Syntax.apply("num", yytext()); }
{sym}       { return Syntax.apply("sym", yytext()); }

[^]         { throw new RuntimeException("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
