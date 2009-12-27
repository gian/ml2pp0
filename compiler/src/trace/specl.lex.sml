functor SpeclLexFun(structure STokens : Specl_TOKENS)  = struct

    structure yyInput : sig

        type stream
	val mkStream : (int -> string) -> stream
	val fromStream : TextIO.StreamIO.instream -> stream
	val getc : stream -> (Char.char * stream) option
	val getpos : stream -> int
	val getlineNo : stream -> int
	val subtract : stream * stream -> string
	val eof : stream -> bool
	val lastWasNL : stream -> bool

      end = struct

        structure TIO = TextIO
        structure TSIO = TIO.StreamIO
	structure TPIO = TextPrimIO

        datatype stream = Stream of {
            strm : TSIO.instream,
	    id : int,  (* track which streams originated 
			* from the same stream *)
	    pos : int,
	    lineNo : int,
	    lastWasNL : bool
          }

	local
	  val next = ref 0
	in
	fun nextId() = !next before (next := !next + 1)
	end

	val initPos = 2 (* ml-lex bug compatibility *)

	fun mkStream inputN = let
              val strm = TSIO.mkInstream 
			   (TPIO.RD {
			        name = "lexgen",
				chunkSize = 4096,
				readVec = SOME inputN,
				readArr = NONE,
				readVecNB = NONE,
				readArrNB = NONE,
				block = NONE,
				canInput = NONE,
				avail = (fn () => NONE),
				getPos = NONE,
				setPos = NONE,
				endPos = NONE,
				verifyPos = NONE,
				close = (fn () => ()),
				ioDesc = NONE
			      }, "")
	      in 
		Stream {strm = strm, id = nextId(), pos = initPos, lineNo = 1,
			lastWasNL = true}
	      end

	fun fromStream strm = Stream {
		strm = strm, id = nextId(), pos = initPos, lineNo = 1, lastWasNL = true
	      }

	fun getc (Stream {strm, pos, id, lineNo, ...}) = (case TSIO.input1 strm
              of NONE => NONE
	       | SOME (c, strm') => 
		   SOME (c, Stream {
			        strm = strm', 
				pos = pos+1, 
				id = id,
				lineNo = lineNo + 
					 (if c = #"\n" then 1 else 0),
				lastWasNL = (c = #"\n")
			      })
	     (* end case*))

	fun getpos (Stream {pos, ...}) = pos

	fun getlineNo (Stream {lineNo, ...}) = lineNo

	fun subtract (new, old) = let
	      val Stream {strm = strm, pos = oldPos, id = oldId, ...} = old
	      val Stream {pos = newPos, id = newId, ...} = new
              val (diff, _) = if newId = oldId andalso newPos >= oldPos
			      then TSIO.inputN (strm, newPos - oldPos)
			      else raise Fail 
				"BUG: yyInput: attempted to subtract incompatible streams"
	      in 
		diff 
	      end

	fun eof s = not (isSome (getc s))

	fun lastWasNL (Stream {lastWasNL, ...}) = lastWasNL

      end

    datatype yystart_state = 
LINECOMMENT | COMMENT | SPECL | INITIAL
    structure UserDeclarations = 
      struct

type pos = int
type svalue = STokens.svalue
type ('a,'b) token = ('a,'b) STokens.token
type lexresult = (svalue,pos) token

fun eof() = STokens.EOF(0,0)

fun someOrFail (SOME x) = x
  | someOrFail NONE = raise (Fail "Invalid Constant!")

val tliteral = ref ""
val tlstart = ref 0



      end

    datatype yymatch 
      = yyNO_MATCH
      | yyMATCH of yyInput.stream * action * yymatch
    withtype action = yyInput.stream * yymatch -> UserDeclarations.lexresult

    local

    val yytable = 
Vector.fromList []
    fun mk yyins = let
        (* current start state *)
        val yyss = ref INITIAL
	fun YYBEGIN ss = (yyss := ss)
	(* current input stream *)
        val yystrm = ref yyins
	(* get one char of input *)
	val yygetc = yyInput.getc
	(* create yytext *)
	fun yymktext(strm) = yyInput.subtract (strm, !yystrm)
        open UserDeclarations
        fun lex 
(yyarg as ()) = let 
     fun continue() = let
            val yylastwasn = yyInput.lastWasNL (!yystrm)
            fun yystuck (yyNO_MATCH) = raise Fail "stuck state"
	      | yystuck (yyMATCH (strm, action, old)) = 
		  action (strm, old)
	    val yypos = yyInput.getpos (!yystrm)
	    val yygetlineNo = yyInput.getlineNo
	    fun yyactsToMatches (strm, [],	  oldMatches) = oldMatches
	      | yyactsToMatches (strm, act::acts, oldMatches) = 
		  yyMATCH (strm, act, yyactsToMatches (strm, acts, oldMatches))
	    fun yygo actTable = 
		(fn (~1, _, oldMatches) => yystuck oldMatches
		  | (curState, strm, oldMatches) => let
		      val (transitions, finals') = Vector.sub (yytable, curState)
		      val finals = map (fn i => Vector.sub (actTable, i)) finals'
		      fun tryfinal() = 
		            yystuck (yyactsToMatches (strm, finals, oldMatches))
		      fun find (c, []) = NONE
			| find (c, (c1, c2, s)::ts) = 
		            if c1 <= c andalso c <= c2 then SOME s
			    else find (c, ts)
		      in case yygetc strm
			  of SOME(c, strm') => 
			       (case find (c, transitions)
				 of NONE => tryfinal()
				  | SOME n => 
				      yygo actTable
					(n, strm', 
					 yyactsToMatches (strm, finals, oldMatches)))
			   | NONE => tryfinal()
		      end)
	    in 
let
fun yyAction0 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN SPECL; continue()))
fun yyAction1 (strm, lastMatch : yymatch) = (yystrm := strm;
      (STokens.OPERATIONS(yypos,yypos + 10)))
fun yyAction2 (strm, lastMatch : yymatch) = (yystrm := strm;
      (STokens.NECESSARY(yypos,yypos + 9)))
fun yyAction3 (strm, lastMatch : yymatch) = (yystrm := strm;
      (STokens.SAFE(yypos,yypos + 4)))
fun yyAction4 (strm, lastMatch : yymatch) = (yystrm := strm;
      (STokens.FORBIDDEN(yypos,yypos + 9)))
fun yyAction5 (strm, lastMatch : yymatch) = (yystrm := strm;
      (STokens.COMMA(yypos,yypos+1)))
fun yyAction6 (strm, lastMatch : yymatch) = (yystrm := strm;
      (STokens.WRITE(yypos,yypos+1)))
fun yyAction7 (strm, lastMatch : yymatch) = (yystrm := strm;
      (STokens.READ(yypos,yypos+1)))
fun yyAction8 (strm, lastMatch : yymatch) = (yystrm := strm;
      (STokens.WILDCARD(yypos,yypos+1)))
fun yyAction9 (strm, lastMatch : yymatch) = (yystrm := strm;
      (STokens.STAR(yypos,yypos+1)))
fun yyAction10 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN LINECOMMENT; continue()))
fun yyAction11 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN COMMENT; continue()))
fun yyAction12 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN SPECL; continue()))
fun yyAction13 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction14 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction15 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN SPECL; continue()))
fun yyAction16 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction17 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (STokens.ACTION(yytext,yypos,yypos+size yytext))
      end
fun yyAction18 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction19 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction20 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (STokens.ERROR(yypos,yypos+size yytext))
      end
fun yyQ3 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yyAction0(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then if yyInput.eof(!(yystrm))
                  then UserDeclarations.eof(yyarg)
                  else yyAction0(strm, yyNO_MATCH)
            else if inp < #"\n"
              then if inp = #"\t"
                  then yyQ3(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
                else if yyInput.eof(!(yystrm))
                  then UserDeclarations.eof(yyarg)
                  else yyAction0(strm, yyNO_MATCH)
            else if inp = #" "
              then yyQ3(strm', yyMATCH(strm, yyAction0, yyNO_MATCH))
            else if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yyAction0(strm, yyNO_MATCH)
      (* end case *))
fun yyQ28 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"("
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ27 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction8(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ28(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"("
                  then yyAction8(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
                      else yyAction8(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction8(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ28(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
                  else yyAction8(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction8(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction8(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
                  else yyAction8(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction8, yyNO_MATCH))
              else yyAction8(strm, yyNO_MATCH)
      (* end case *))
fun yyQ31 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction3(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ28(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"("
                  then yyAction3(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                      else yyAction3(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction3(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ28(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                  else yyAction3(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction3(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction3(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
                  else yyAction3(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction3, yyNO_MATCH))
              else yyAction3(strm, yyNO_MATCH)
      (* end case *))
fun yyQ30 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"E"
              then yyQ31(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"E"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ29 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"F"
              then yyQ30(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"F"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ26 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"B"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"B"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ29(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ40 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction1(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ28(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"("
                  then yyAction1(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
                      else yyAction1(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction1(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ28(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
                  else yyAction1(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction1(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction1(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
                  else yyAction1(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction1, yyNO_MATCH))
              else yyAction1(strm, yyNO_MATCH)
      (* end case *))
fun yyQ39 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"S"
              then yyQ40(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"S"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ38 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"N"
              then yyQ39(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"N"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ37 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"O"
              then yyQ38(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"O"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ36 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"I"
              then yyQ37(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"I"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ35 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"T"
              then yyQ36(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"T"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ34 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"B"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"B"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ35(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ33 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"R"
              then yyQ34(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"R"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ32 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"E"
              then yyQ33(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"E"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ25 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"P"
              then yyQ32(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"P"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ48 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction2(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ28(strm', yyMATCH(strm, yyAction2, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"("
                  then yyAction2(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction2, yyNO_MATCH))
                      else yyAction2(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction2, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction2(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ28(strm', yyMATCH(strm, yyAction2, yyNO_MATCH))
                  else yyAction2(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction2(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction2(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction2, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction2, yyNO_MATCH))
                  else yyAction2(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction2, yyNO_MATCH))
              else yyAction2(strm, yyNO_MATCH)
      (* end case *))
fun yyQ47 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"Y"
              then yyQ48(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"Y"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ46 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"R"
              then yyQ47(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"R"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ45 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"B"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"B"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ46(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ44 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"S"
              then yyQ45(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"S"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ43 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"S"
              then yyQ44(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"S"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ42 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"E"
              then yyQ43(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"E"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ41 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"C"
              then yyQ42(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"C"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ24 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"E"
              then yyQ41(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"E"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ56 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction4(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ28(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"("
                  then yyAction4(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                      else yyAction4(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction4(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ28(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                  else yyAction4(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction4(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction4(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
                  else yyAction4(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction4, yyNO_MATCH))
              else yyAction4(strm, yyNO_MATCH)
      (* end case *))
fun yyQ55 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"N"
              then yyQ56(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"N"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ54 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"E"
              then yyQ55(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"E"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ53 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"D"
              then yyQ54(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"D"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ52 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"D"
              then yyQ53(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"D"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ51 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"I"
              then yyQ52(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"I"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ50 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"B"
              then yyQ51(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"B"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"A"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ49 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"R"
              then yyQ50(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"R"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ23 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"O"
              then yyQ49(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"O"
              then if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #":"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #":"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp <= #"@"
                  then yyAction17(strm, yyNO_MATCH)
                  else yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ22 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction7(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction7(strm, yyNO_MATCH)
      (* end case *))
fun yyQ21 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction5(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction5(strm, yyNO_MATCH)
      (* end case *))
fun yyQ20 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction9(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction9(strm, yyNO_MATCH)
      (* end case *))
fun yyQ57 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction11(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction11(strm, yyNO_MATCH)
      (* end case *))
fun yyQ19 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction20(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"*"
              then yyQ57(strm', yyMATCH(strm, yyAction20, yyNO_MATCH))
              else yyAction20(strm, yyNO_MATCH)
      (* end case *))
fun yyQ18 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction17(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"A"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
            else if inp < #"A"
              then if inp = #"("
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"("
                  then if inp = #"'"
                      then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                      else yyAction17(strm, yyNO_MATCH)
                else if inp = #"0"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp < #"0"
                  then yyAction17(strm, yyNO_MATCH)
                else if inp <= #"9"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp = #"`"
              then yyAction17(strm, yyNO_MATCH)
            else if inp < #"`"
              then if inp = #"["
                  then yyAction17(strm, yyNO_MATCH)
                else if inp < #"["
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                else if inp = #"_"
                  then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
                  else yyAction17(strm, yyNO_MATCH)
            else if inp <= #"z"
              then yyQ28(strm', yyMATCH(strm, yyAction17, yyNO_MATCH))
              else yyAction17(strm, yyNO_MATCH)
      (* end case *))
fun yyQ17 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction10(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction10(strm, yyNO_MATCH)
      (* end case *))
fun yyQ16 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction6(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction6(strm, yyNO_MATCH)
      (* end case *))
fun yyQ15 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction18(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction18(strm, yyNO_MATCH)
      (* end case *))
fun yyQ14 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction18(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction18(strm, yyNO_MATCH)
      (* end case *))
fun yyQ58 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction19(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyAction19(strm, yyNO_MATCH)
            else if inp < #"\n"
              then if inp = #"\t"
                  then yyQ58(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                  else yyAction19(strm, yyNO_MATCH)
            else if inp = #" "
              then yyQ58(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
              else yyAction19(strm, yyNO_MATCH)
      (* end case *))
fun yyQ13 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction19(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #"\n"
              then yyAction19(strm, yyNO_MATCH)
            else if inp < #"\n"
              then if inp = #"\t"
                  then yyQ58(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                  else yyAction19(strm, yyNO_MATCH)
            else if inp = #" "
              then yyQ58(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
              else yyAction19(strm, yyNO_MATCH)
      (* end case *))
fun yyQ12 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction20(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction20(strm, yyNO_MATCH)
      (* end case *))
fun yyQ2 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yyAction19(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #","
              then yyQ21(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp < #","
              then if inp = #"\""
                  then yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                else if inp < #"\""
                  then if inp = #"\r"
                      then yyQ15(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                    else if inp < #"\r"
                      then if inp = #"\n"
                          then yyQ14(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                        else if inp < #"\n"
                          then if inp = #"\t"
                              then yyQ13(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                              else yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                          else yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                    else if inp = #" "
                      then yyQ13(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                    else if inp = #"!"
                      then yyQ16(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                      else yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                else if inp = #"("
                  then yyQ19(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                else if inp < #"("
                  then if inp = #"$"
                      then yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                    else if inp < #"$"
                      then yyQ17(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                    else if inp = #"'"
                      then yyQ18(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                      else yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                else if inp = #"*"
                  then yyQ20(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                  else yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp = #"P"
              then yyQ18(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp < #"P"
              then if inp = #"F"
                  then yyQ23(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                else if inp < #"F"
                  then if inp = #"@"
                      then yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                    else if inp < #"@"
                      then if inp = #"?"
                          then yyQ22(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                          else yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                      else yyQ18(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                else if inp = #"N"
                  then yyQ24(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                else if inp = #"O"
                  then yyQ25(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                  else yyQ18(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp = #"_"
              then yyQ27(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp < #"_"
              then if inp = #"T"
                  then yyQ18(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                else if inp < #"T"
                  then if inp = #"S"
                      then yyQ26(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                      else yyQ18(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                else if inp <= #"Z"
                  then yyQ18(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
                  else yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp = #"a"
              then yyQ18(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp < #"a"
              then yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
            else if inp <= #"z"
              then yyQ18(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
              else yyQ12(strm', yyMATCH(strm, yyAction19, yyNO_MATCH))
      (* end case *))
fun yyQ11 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction12(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction12(strm, yyNO_MATCH)
      (* end case *))
fun yyQ10 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction14(strm, yyNO_MATCH)
        | SOME(inp, strm') =>
            if inp = #")"
              then yyQ11(strm', yyMATCH(strm, yyAction14, yyNO_MATCH))
              else yyAction14(strm, yyNO_MATCH)
      (* end case *))
fun yyQ9 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction13(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction13(strm, yyNO_MATCH)
      (* end case *))
fun yyQ8 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction13(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction13(strm, yyNO_MATCH)
      (* end case *))
fun yyQ7 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction14(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction14(strm, yyNO_MATCH)
      (* end case *))
fun yyQ1 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"\r"
              then yyQ9(strm', lastMatch)
            else if inp < #"\r"
              then if inp = #"\n"
                  then yyQ8(strm', lastMatch)
                  else yyQ7(strm', lastMatch)
            else if inp = #"*"
              then yyQ10(strm', lastMatch)
              else yyQ7(strm', lastMatch)
      (* end case *))
fun yyQ6 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction15(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction15(strm, yyNO_MATCH)
      (* end case *))
fun yyQ5 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction15(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction15(strm, yyNO_MATCH)
      (* end case *))
fun yyQ4 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE => yyAction16(strm, yyNO_MATCH)
        | SOME(inp, strm') => yyAction16(strm, yyNO_MATCH)
      (* end case *))
fun yyQ0 (strm, lastMatch : yymatch) = (case (yygetc(strm))
       of NONE =>
            if yyInput.eof(!(yystrm))
              then UserDeclarations.eof(yyarg)
              else yystuck(lastMatch)
        | SOME(inp, strm') =>
            if inp = #"\v"
              then yyQ4(strm', lastMatch)
            else if inp < #"\v"
              then if inp = #"\n"
                  then yyQ5(strm', lastMatch)
                  else yyQ4(strm', lastMatch)
            else if inp = #"\r"
              then yyQ6(strm', lastMatch)
              else yyQ4(strm', lastMatch)
      (* end case *))
in
  (case (!(yyss))
   of LINECOMMENT => yyQ0(!(yystrm), yyNO_MATCH)
    | COMMENT => yyQ1(!(yystrm), yyNO_MATCH)
    | SPECL => yyQ2(!(yystrm), yyNO_MATCH)
    | INITIAL => yyQ3(!(yystrm), yyNO_MATCH)
  (* end case *))
end
            end
	  in 
            continue() 	  
	    handle IO.Io{cause, ...} => raise cause
          end
        in 
          lex 
        end
    in
    fun makeLexer yyinputN = mk (yyInput.mkStream yyinputN)
    fun makeLexer' ins = mk (yyInput.mkStream ins)
    end

  end
