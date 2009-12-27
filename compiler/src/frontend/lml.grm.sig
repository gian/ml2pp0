signature Lml_TOKENS =
sig
type ('a,'b) token
type svalue
val EOF:  'a * 'a -> (svalue,'a) token
val ERROR:  'a * 'a -> (svalue,'a) token
val LSTR: (string) *  'a * 'a -> (svalue,'a) token
val SEMI:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val CONS:  'a * 'a -> (svalue,'a) token
val RSQ:  'a * 'a -> (svalue,'a) token
val LSQ:  'a * 'a -> (svalue,'a) token
val RBR:  'a * 'a -> (svalue,'a) token
val LBR:  'a * 'a -> (svalue,'a) token
val RPAR:  'a * 'a -> (svalue,'a) token
val LPAR:  'a * 'a -> (svalue,'a) token
val IDENT: (string) *  'a * 'a -> (svalue,'a) token
val TYPEDELIM:  'a * 'a -> (svalue,'a) token
val CLAUSE:  'a * 'a -> (svalue,'a) token
val UMINUS:  'a * 'a -> (svalue,'a) token
val BNOT:  'a * 'a -> (svalue,'a) token
val BOR:  'a * 'a -> (svalue,'a) token
val BAND:  'a * 'a -> (svalue,'a) token
val FN:  'a * 'a -> (svalue,'a) token
val GT:  'a * 'a -> (svalue,'a) token
val LT:  'a * 'a -> (svalue,'a) token
val GTEQ:  'a * 'a -> (svalue,'a) token
val LTEQ:  'a * 'a -> (svalue,'a) token
val ARROW:  'a * 'a -> (svalue,'a) token
val MUTASSIGN:  'a * 'a -> (svalue,'a) token
val FNASSIGN:  'a * 'a -> (svalue,'a) token
val NEQ:  'a * 'a -> (svalue,'a) token
val EQUALS:  'a * 'a -> (svalue,'a) token
val DIVIDE:  'a * 'a -> (svalue,'a) token
val TIMES:  'a * 'a -> (svalue,'a) token
val MINUS:  'a * 'a -> (svalue,'a) token
val PLUS:  'a * 'a -> (svalue,'a) token
val ASCRIBEO:  'a * 'a -> (svalue,'a) token
val BTYPECHOICE:  'a * 'a -> (svalue,'a) token
val BTYPECOMP:  'a * 'a -> (svalue,'a) token
val BANG:  'a * 'a -> (svalue,'a) token
val BTYPERECV:  'a * 'a -> (svalue,'a) token
val BTYPEEND:  'a * 'a -> (svalue,'a) token
val BTYPESTART:  'a * 'a -> (svalue,'a) token
val LREAL: (real) *  'a * 'a -> (svalue,'a) token
val LINT: (int) *  'a * 'a -> (svalue,'a) token
val END:  'a * 'a -> (svalue,'a) token
val IN:  'a * 'a -> (svalue,'a) token
val LET:  'a * 'a -> (svalue,'a) token
val TYPE:  'a * 'a -> (svalue,'a) token
val OF:  'a * 'a -> (svalue,'a) token
val FALSE:  'a * 'a -> (svalue,'a) token
val TRUE:  'a * 'a -> (svalue,'a) token
val DATATYPE:  'a * 'a -> (svalue,'a) token
val FUN:  'a * 'a -> (svalue,'a) token
val NIL:  'a * 'a -> (svalue,'a) token
val ELSE:  'a * 'a -> (svalue,'a) token
val THEN:  'a * 'a -> (svalue,'a) token
val IF:  'a * 'a -> (svalue,'a) token
val SIGNATURE:  'a * 'a -> (svalue,'a) token
val SIG:  'a * 'a -> (svalue,'a) token
val STRUCTURE:  'a * 'a -> (svalue,'a) token
val STRUCT:  'a * 'a -> (svalue,'a) token
val VAL:  'a * 'a -> (svalue,'a) token
end
signature Lml_LRVALS=
sig
structure Tokens : Lml_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
