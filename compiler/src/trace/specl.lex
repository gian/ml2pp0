type pos = int
type svalue = STokens.svalue
type ('a,'b) token = ('a,'b) STokens.token
type lexresult = (svalue,pos) token

fun eof() = STokens.EOF(0,0)

fun someOrFail (SOME x) = x
  | someOrFail NONE = raise (Fail "Invalid Constant!")

val tliteral = ref ""
val tlstart = ref 0

%%
%header (functor SpeclLexFun(structure STokens : Specl_TOKENS));

%s SPECL LINECOMMENT COMMENT;

digits=[0-9]+;
ident=['a-zA-Z_][a-zA-Z0-9_']*;
ws=[\ \t];
eol=[\n\r];
%%
<INITIAL>{ws}*		=> (YYBEGIN SPECL; continue());

<SPECL>"OPERATIONS"	=> (STokens.OPERATIONS(yypos,yypos + 10));
<SPECL>"NECESSARY"	=> (STokens.NECESSARY(yypos,yypos + 9));
<SPECL>"SAFE"		=> (STokens.SAFE(yypos,yypos + 4));
<SPECL>"FORBIDDEN"	=> (STokens.FORBIDDEN(yypos,yypos + 9));

<SPECL>","		=> (STokens.COMMA(yypos,yypos+1));
<SPECL>"!"		=> (STokens.WRITE(yypos,yypos+1));
<SPECL>"?"		=> (STokens.READ(yypos,yypos+1));
<SPECL>"_"		=> (STokens.WILDCARD(yypos,yypos+1));
<SPECL>"*"		=> (STokens.STAR(yypos,yypos+1));

<SPECL>"#"              => (YYBEGIN LINECOMMENT; continue());
<SPECL>"(*"		=> (YYBEGIN COMMENT; continue());

<COMMENT>"*)"		=> (YYBEGIN SPECL; continue());
<COMMENT>{eol}		=> (continue());
<COMMENT>.		=> (continue());

<LINECOMMENT>{eol}	=> (YYBEGIN SPECL; continue());
<LINECOMMENT>.		=> (continue());

<SPECL>{ident}		=> (STokens.ACTION(yytext,yypos,yypos+size yytext));

<SPECL>{eol}		=> (continue());
<SPECL>{ws}*		=> (continue());
<SPECL>.		=> (STokens.ERROR(yypos,yypos+size yytext));

