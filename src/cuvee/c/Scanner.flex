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

// integer constants, decimal, octal, or hexadecimal, with suffixes u, l, ll in any order and case,
// and character constants, which the parser converts to their values (see Parser.literal)
dec = [1-9][0-9]* | 0
oct = 0[0-7]+
hex = 0[xX][0-9a-fA-F]+
suffix = [uU]? ([lL] | "ll" | "LL")? | ([lL] | "ll" | "LL") [uU]
chr = \' ([^\'\\\n] | \\[^0-7x\n] | \\[0-7]{1,3} | \\x[0-9a-fA-F]+) \'

num  = ({dec} | {oct} | {hex}) {suffix} | {chr}

// type qualifiers and storage classes are ignored by the grammar, as are attributes of GCC
kw  = "int" | "long" | "short" | "char" | "unsigned" | "signed" | "_Bool" | "bool" | "void" | "float" | "double"
    | "const" | "static" | "extern" | "volatile" | "inline" | "restrict" | "__attribute__"
    | "typedef" | "sizeof"
    | "if" | "else" | "while" | "do" | "for" | "break" | "continue" | "return" | "goto"
    | "switch" | "case" | "default"
    | "(" | ")" | "[" | "]" | [;,{}?:]
    | "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "&=" | "|=" | "^=" | "<<=" | ">>=" | "++" | "--"

// string literals, which occur in the harness of SV-COMP, e.g. as arguments of __assert_fail
str = \" ([^\"\\\n] | \\.)* \"

id  = [a-zA-Z_] [a-zA-Z0-9_]*
sym = {id}
    | [+\-*/%!<>&|\^~] | "&&" | "||" | "==" | "!=" | "<=" | ">=" | "<<" | ">>"

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

[^]         { Syntax.error("unexpected character '" + yytext() + "' at " + yyline + ":" + yycolumn); }

}
