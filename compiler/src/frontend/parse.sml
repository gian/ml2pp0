structure Parse : sig val parse : string -> Ast.program end =
struct 
  structure MLLrVals = MLLrValsFun(structure Token = LrParser.Token)
  structure Lex = MLLexFun(structure Tokens = MLLrVals.Tokens)
  structure MlP = Join(structure ParserData = MLLrVals.ParserData
			structure Lex=Lex
			structure LrParser = LrParser)
  fun parse' filename = let
	  val file = TextIO.openIn filename
	  fun get _ = TextIO.input file
	  fun parseerror(s,p1,p2) = print ("Parse Error\n") 
	  val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
	  val (absyn,_) = MlP.parse(30,lexer,parseerror,())
       in TextIO.closeIn file;
	    absyn
      end  

  fun parse filename = raise (Fail "Old style AST call")

end


