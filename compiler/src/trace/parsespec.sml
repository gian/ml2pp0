structure ParseSpec : sig val parse : string -> Spec.spec end =
struct
  structure SpeclLrVals = SpeclLrValsFun(structure Token = LrParser.Token)
  structure Lex = SpeclLexFun(structure STokens = SpeclLrVals.Tokens)
  structure SpeclP = Join(structure ParserData = SpeclLrVals.ParserData
                        structure Lex=Lex
                        structure LrParser = LrParser)

  fun parse filename = let
          val file = TextIO.openIn filename
          fun get _ = TextIO.input file
          fun parseerror(s,p1,p2) = print ("Parse Error at " ^ (Int.toString p1) ^ "-" ^ (Int.toString p2) ^ ": " ^ s ^ "\n")
          val lexer = LrParser.Stream.streamify (Lex.makeLexer get)
          val (sp,_) = SpeclP.parse(30,lexer,parseerror,())
       in TextIO.closeIn file;
          sp
      end
end
