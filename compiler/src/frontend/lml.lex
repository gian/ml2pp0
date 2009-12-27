type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue,pos) token

fun eof() = Tokens.EOF(0,0)

fun someOrFail (SOME x) = x
  | someOrFail NONE = raise (Fail "Invalid Constant!")

val tliteral = ref ""
val tlstart = ref 0

%%
%header (functor LmlLexFun(structure Tokens : Lml_TOKENS));

%s LML LINECOMMENT COMMENT HTML XML STRINGLIT EMLML;

digits=[0-9]+;
real=([0-9]+"."[0-9]*)|([0-9]*"."[0-9]+);
ident=['a-zA-Z_][a-zA-Z0-9_']*;
stringlit="\""([^\"]*)"\"";
ws=[\ \t];
eol=[\n\r];
%%
<INITIAL>{ws}*		=> (YYBEGIN LML; continue());

<LML>"val"		=> (Tokens.VAL(yypos,yypos+3));
<LML>"struct"		=> (Tokens.STRUCT(yypos,yypos+3));
<LML>"structure"	=> (Tokens.STRUCTURE(yypos,yypos+9));
<LML>"sig"		=> (Tokens.SIG(yypos,yypos+3));
<LML>"signature"	=> (Tokens.SIGNATURE(yypos,yypos+9));
<LML>"if"		=> (Tokens.IF(yypos,yypos+2));
<LML>"then"		=> (Tokens.THEN(yypos,yypos+2));
<LML>"else"		=> (Tokens.ELSE(yypos,yypos+4));
<LML>"nil"             => (Tokens.NIL(yypos,yypos+3));
<LML>"datatype"		=> (Tokens.DATATYPE(yypos,yypos+8));
<LML>"of"		=> (Tokens.OF(yypos,yypos+2));
<LML>"type"		=> (Tokens.TYPE(yypos,yypos+4));
<LML>"fun"           => (Tokens.FUN(yypos,yypos+3));
<LML>"let"           => (Tokens.LET(yypos,yypos+3));
<LML>"in"           => (Tokens.IN(yypos,yypos+2));
<LML>"end"           => (Tokens.END(yypos,yypos+3));
<LML>"not"	     => (Tokens.BNOT(yypos,yypos+3));
<LML>"true"	     => (Tokens.TRUE(yypos,yypos+4));
<LML>"false"	     => (Tokens.FALSE(yypos,yypos+5));

<LML>{digits}		=> (Tokens.LINT(someOrFail(Int.fromString yytext),yypos,yypos+size yytext));
<LML>{real}		=> (Tokens.LREAL(someOrFail(Real.fromString yytext),yypos,yypos+size yytext));
<LML>"\""		=> (YYBEGIN STRINGLIT; tlstart := yypos; tliteral := ""; continue());

<LML>"-("		=> (Tokens.BTYPESTART(yypos,yypos+2));
<LML>"?"		=> (Tokens.BTYPERECV(yypos,yypos+1));
<LML>"!"		=> (Tokens.BANG(yypos,yypos+1));
<LML>"||"		=> (Tokens.BTYPECOMP(yypos,yypos+2));
<LML>"#"		=> (Tokens.BTYPECHOICE(yypos,yypos+1));
<LML>")->"		=> (Tokens.BTYPEEND(yypos,yypos+3));

<LML>"->"		=> (Tokens.ARROW(yypos,yypos+2));
<LML>":>"		=> (Tokens.ASCRIBEO(yypos,yypos+2));
<LML>"+"		=> (Tokens.PLUS(yypos,yypos+1));
<LML>"-"		=> (Tokens.MINUS(yypos,yypos+1));
<LML>"*"		=> (Tokens.TIMES(yypos,yypos+1));
<LML>"/"		=> (Tokens.DIVIDE(yypos,yypos+1));
<LML>"="		=> (Tokens.EQUALS(yypos,yypos+2));
<LML>"~"		=> (Tokens.UMINUS(yypos,yypos+1));
<LML>"<>"		=> (Tokens.NEQ(yypos,yypos+2));
<LML>"=>"		=> (Tokens.FNASSIGN(yypos,yypos+2));
<LML>"<="		=> (Tokens.LTEQ(yypos,yypos+2));
<LML>">="		=> (Tokens.GTEQ(yypos,yypos+2));
<LML>"<"		=> (Tokens.LT(yypos,yypos+1));
<LML>">"		=> (Tokens.GT(yypos,yypos+1));
<LML>"fn"		=> (Tokens.FN(yypos,yypos+1));
<LML>"andalso"		=> (Tokens.BAND(yypos,yypos+7));
<LML>"orelse"		=> (Tokens.BOR(yypos,yypos+6));
<LML>"|"              	=> (Tokens.CLAUSE(yypos,yypos+1));
<LML>"::"              	=> (Tokens.CONS(yypos,yypos+2));
<LML>":="		=> (Tokens.MUTASSIGN(yypos,yypos+2));
<LML>":"              	=> (Tokens.TYPEDELIM(yypos,yypos+1));

<LML>"("		=> (Tokens.LPAR(yypos,yypos+1));
<LML>")"		=> (Tokens.RPAR(yypos,yypos+1));
<LML>"{"		=> (Tokens.LBR(yypos,yypos+1));
<LML>"}"		=> (Tokens.RBR(yypos,yypos+1));
<LML>"["		=> (Tokens.LSQ(yypos,yypos+1));
<LML>"]"		=> (Tokens.RSQ(yypos,yypos+1));
<LML>","		=> (Tokens.COMMA(yypos,yypos+1));
<LML>";"		=> (Tokens.SEMI(yypos,yypos+1));

<LML>"(*"		=> (YYBEGIN COMMENT; continue());

<COMMENT>"*)"		=> (YYBEGIN LML; continue());
<COMMENT>{eol}		=> (continue());
<COMMENT>.		=> (continue());

<STRINGLIT>"\""		=> (YYBEGIN LML; Tokens.LSTR(!tliteral,!tlstart,!tlstart + size (!tliteral)));
<STRINGLIT>{eol}	=> (Tokens.ERROR(!tlstart,yypos));
<STRINGLIT>.		=> (tliteral := !tliteral ^ yytext; continue());

<LML>{ident}		=> (Tokens.IDENT(yytext,yypos,yypos+size yytext));

<LML>{eol}		=> (continue());
<LML>{ws}*		=> (continue());
<LML>.			=> (Tokens.ERROR(yypos,yypos+size yytext));

