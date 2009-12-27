signature Specl_TOKENS =
sig
type ('a,'b) token
type svalue
val EOF:  'a * 'a -> (svalue,'a) token
val ERROR:  'a * 'a -> (svalue,'a) token
val ACTION: (string) *  'a * 'a -> (svalue,'a) token
val STAR:  'a * 'a -> (svalue,'a) token
val WILDCARD:  'a * 'a -> (svalue,'a) token
val READ:  'a * 'a -> (svalue,'a) token
val WRITE:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val FORBIDDEN:  'a * 'a -> (svalue,'a) token
val SAFE:  'a * 'a -> (svalue,'a) token
val NECESSARY:  'a * 'a -> (svalue,'a) token
val OPERATIONS:  'a * 'a -> (svalue,'a) token
end
signature Specl_LRVALS=
sig
structure Tokens : Specl_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
