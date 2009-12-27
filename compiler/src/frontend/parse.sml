structure Parse : sig val parse : string -> Absyn.stm list end =
struct 
  structure LmlLrVals = LmlLrValsFun(structure Token = LrParser.Token)
  structure Lex = LmlLexFun(structure Tokens = LmlLrVals.Tokens)
  structure LmlP = Join(structure ParserData = LmlLrVals.ParserData
			structure Lex=Lex
			structure LrParser = LrParser)
  fun parse filename = let
	  val file = TextIO.openIn filename
	  fun get _ = TextIO.input file
	  fun parseerror(s,p1,p2) = print ("Parse Error at " ^ (Int.toString p1) ^ "-" ^ (Int.toString p2) ^ ": " ^ s ^ "\n") 
	  val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
	  val (absyn,_) = LmlP.parse(30,lexer,parseerror,())
       in TextIO.closeIn file;
	    absyn
      end  

end


