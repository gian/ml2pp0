functor SpeclLrValsFun(structure Token : TOKEN)
 : sig structure ParserData : PARSER_DATA
       structure Tokens : Specl_TOKENS
   end
 = 
struct
structure ParserData=
struct
structure Header = 
struct
(* Specl - Little Specification Language *)
(* Copyright (c) 2008 Gian Perrone *)
(* gdp3 at cs.waikato.ac.nz *)

structure S = Spec


end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\003\000\000\000\
\\001\000\002\000\009\000\000\000\
\\001\000\003\000\037\000\004\000\037\000\008\000\007\000\010\000\006\000\
\\012\000\037\000\000\000\
\\001\000\003\000\022\000\000\000\
\\001\000\004\000\025\000\000\000\
\\001\000\008\000\007\000\010\000\006\000\000\000\
\\001\000\010\000\017\000\000\000\
\\001\000\010\000\018\000\000\000\
\\001\000\012\000\000\000\000\000\
\\001\000\012\000\027\000\000\000\
\\029\000\000\000\
\\030\000\006\000\011\000\007\000\010\000\000\000\
\\031\000\000\000\
\\032\000\000\000\
\\033\000\000\000\
\\034\000\008\000\007\000\010\000\006\000\000\000\
\\035\000\000\000\
\\036\000\000\000\
\\038\000\000\000\
\\039\000\008\000\007\000\010\000\006\000\000\000\
\\040\000\005\000\020\000\000\000\
\\041\000\000\000\
\\042\000\000\000\
\\043\000\009\000\019\000\000\000\
\"
val actionRowNumbers =
"\000\000\005\000\015\000\001\000\
\\011\000\014\000\016\000\019\000\
\\006\000\007\000\023\000\020\000\
\\002\000\017\000\003\000\013\000\
\\012\000\022\000\005\000\018\000\
\\019\000\021\000\004\000\019\000\
\\009\000\010\000\008\000"
val gotoT =
"\
\\001\000\026\000\000\000\
\\002\000\003\000\008\000\002\000\000\000\
\\002\000\006\000\008\000\002\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\003\000\014\000\005\000\013\000\006\000\012\000\007\000\011\000\
\\008\000\010\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\019\000\006\000\012\000\007\000\011\000\008\000\010\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\006\000\021\000\007\000\011\000\008\000\010\000\000\000\
\\000\000\
\\005\000\022\000\006\000\012\000\007\000\011\000\008\000\010\000\000\000\
\\000\000\
\\000\000\
\\005\000\024\000\006\000\012\000\007\000\011\000\008\000\010\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 27
val numrules = 15
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = int
type arg = unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit ->  unit
 | ACTION of unit ->  (string) | action of unit ->  (S.action)
 | traceel of unit ->  (S.action SpecBuilder.trace_element)
 | trace of unit ->  (S.action SpecBuilder.trace_element SpecBuilder.trace)
 | traces of unit ->  (S.action SpecBuilder.trace_element SpecBuilder.trace list)
 | fsection of unit ->  (S.action SpecBuilder.trace list)
 | section of unit ->  (S.action SpecBuilder.trace_element SpecBuilder.trace list)
 | opsection of unit ->  (S.action list) | spec of unit ->  (S.spec)
end
type svalue = MlyValue.svalue
type result = S.spec
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 11) => true | _ => false
val showTerminal =
fn (T 0) => "OPERATIONS"
  | (T 1) => "NECESSARY"
  | (T 2) => "SAFE"
  | (T 3) => "FORBIDDEN"
  | (T 4) => "COMMA"
  | (T 5) => "WRITE"
  | (T 6) => "READ"
  | (T 7) => "WILDCARD"
  | (T 8) => "STAR"
  | (T 9) => "ACTION"
  | (T 10) => "ERROR"
  | (T 11) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 11) $$ (T 10) $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ 
(T 3) $$ (T 2) $$ (T 1) $$ (T 0)end
structure Actions =
struct 
type int = Int.int
exception mlyAction of int
local open Header in
val actions = 
fn (i392:int,defaultPos,stack,
    (()):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( _, _, EOF1right)) :: ( _, ( MlyValue.traces traces2,
 _, _)) :: _ :: ( _, ( MlyValue.traces traces1, _, _)) :: _ :: ( _, ( 
MlyValue.section section1, _, _)) :: _ :: ( _, ( MlyValue.opsection 
opsection1, _, _)) :: ( _, ( _, OPERATIONS1left, _)) :: rest671)) =>
 let val  result = MlyValue.spec (fn _ => let val  (opsection as 
opsection1) = opsection1 ()
 val  section1 = section1 ()
 val  traces1 = traces1 ()
 val  traces2 = traces2 ()
 in (
{operations=opsection,necessary=section1,safe=traces1,forbidden=traces2}
)
end)
 in ( LrTable.NT 0, ( result, OPERATIONS1left, EOF1right), rest671)

end
|  ( 1, ( ( _, ( MlyValue.ACTION ACTION1, ACTION1left, ACTION1right))
 :: rest671)) => let val  result = MlyValue.action (fn _ => let val  (
ACTION as ACTION1) = ACTION1 ()
 in (S.Label ACTION)
end)
 in ( LrTable.NT 7, ( result, ACTION1left, ACTION1right), rest671)
end
|  ( 2, ( ( _, ( MlyValue.ACTION ACTION2, _, ACTION2right)) :: _ :: (
 _, ( MlyValue.ACTION ACTION1, ACTION1left, _)) :: rest671)) => let
 val  result = MlyValue.action (fn _ => let val  ACTION1 = ACTION1 ()
 val  ACTION2 = ACTION2 ()
 in (S.Write (ACTION1,ACTION2))
end)
 in ( LrTable.NT 7, ( result, ACTION1left, ACTION2right), rest671)
end
|  ( 3, ( ( _, ( MlyValue.ACTION ACTION2, _, ACTION2right)) :: _ :: (
 _, ( MlyValue.ACTION ACTION1, ACTION1left, _)) :: rest671)) => let
 val  result = MlyValue.action (fn _ => let val  ACTION1 = ACTION1 ()
 val  ACTION2 = ACTION2 ()
 in (S.Read (ACTION1,ACTION2))
end)
 in ( LrTable.NT 7, ( result, ACTION1left, ACTION2right), rest671)
end
|  ( 4, ( ( _, ( _, WILDCARD1left, WILDCARD1right)) :: rest671)) =>
 let val  result = MlyValue.action (fn _ => (S.Wildcard))
 in ( LrTable.NT 7, ( result, WILDCARD1left, WILDCARD1right), rest671)

end
|  ( 5, ( ( _, ( MlyValue.action action1, action1left, action1right))
 :: rest671)) => let val  result = MlyValue.opsection (fn _ => let
 val  (action as action1) = action1 ()
 in ([action])
end)
 in ( LrTable.NT 1, ( result, action1left, action1right), rest671)
end
|  ( 6, ( ( _, ( MlyValue.opsection opsection1, _, opsection1right))
 :: ( _, ( MlyValue.action action1, action1left, _)) :: rest671)) =>
 let val  result = MlyValue.opsection (fn _ => let val  (action as 
action1) = action1 ()
 val  (opsection as opsection1) = opsection1 ()
 in (action :: opsection)
end)
 in ( LrTable.NT 1, ( result, action1left, opsection1right), rest671)

end
|  ( 7, ( ( _, ( MlyValue.traces traces1, traces1left, traces1right))
 :: rest671)) => let val  result = MlyValue.section (fn _ => let val 
 (traces as traces1) = traces1 ()
 in (traces)
end)
 in ( LrTable.NT 2, ( result, traces1left, traces1right), rest671)
end
|  ( 8, ( ( _, ( MlyValue.trace trace1, trace1left, trace1right)) :: 
rest671)) => let val  result = MlyValue.traces (fn _ => let val  (
trace as trace1) = trace1 ()
 in ([trace])
end)
 in ( LrTable.NT 4, ( result, trace1left, trace1right), rest671)
end
|  ( 9, ( ( _, ( MlyValue.traces traces1, _, traces1right)) :: ( _, ( 
MlyValue.trace trace1, trace1left, _)) :: rest671)) => let val  result
 = MlyValue.traces (fn _ => let val  (trace as trace1) = trace1 ()
 val  (traces as traces1) = traces1 ()
 in (trace :: traces)
end)
 in ( LrTable.NT 4, ( result, trace1left, traces1right), rest671)
end
|  ( 10, ( rest671)) => let val  result = MlyValue.traces (fn _ => ([]
))
 in ( LrTable.NT 4, ( result, defaultPos, defaultPos), rest671)
end
|  ( 11, ( ( _, ( MlyValue.traceel traceel1, traceel1left, 
traceel1right)) :: rest671)) => let val  result = MlyValue.trace (fn _
 => let val  (traceel as traceel1) = traceel1 ()
 in ([traceel])
end)
 in ( LrTable.NT 5, ( result, traceel1left, traceel1right), rest671)

end
|  ( 12, ( ( _, ( MlyValue.trace trace1, _, trace1right)) :: _ :: ( _,
 ( MlyValue.traceel traceel1, traceel1left, _)) :: rest671)) => let
 val  result = MlyValue.trace (fn _ => let val  (traceel as traceel1)
 = traceel1 ()
 val  (trace as trace1) = trace1 ()
 in (traceel :: trace)
end)
 in ( LrTable.NT 5, ( result, traceel1left, trace1right), rest671)
end
|  ( 13, ( ( _, ( _, _, STAR1right)) :: ( _, ( MlyValue.action action1
, action1left, _)) :: rest671)) => let val  result = MlyValue.traceel
 (fn _ => let val  (action as action1) = action1 ()
 in ((action,SOME SpecBuilder.Star))
end)
 in ( LrTable.NT 6, ( result, action1left, STAR1right), rest671)
end
|  ( 14, ( ( _, ( MlyValue.action action1, action1left, action1right))
 :: rest671)) => let val  result = MlyValue.traceel (fn _ => let val 
 (action as action1) = action1 ()
 in ((action,NONE))
end)
 in ( LrTable.NT 6, ( result, action1left, action1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.spec x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a ()
end
end
structure Tokens : Specl_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun OPERATIONS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(
ParserData.MlyValue.VOID,p1,p2))
fun NECESSARY (p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(
ParserData.MlyValue.VOID,p1,p2))
fun SAFE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(
ParserData.MlyValue.VOID,p1,p2))
fun FORBIDDEN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(
ParserData.MlyValue.VOID,p1,p2))
fun COMMA (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(
ParserData.MlyValue.VOID,p1,p2))
fun WRITE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(
ParserData.MlyValue.VOID,p1,p2))
fun READ (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(
ParserData.MlyValue.VOID,p1,p2))
fun WILDCARD (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(
ParserData.MlyValue.VOID,p1,p2))
fun STAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(
ParserData.MlyValue.VOID,p1,p2))
fun ACTION (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(
ParserData.MlyValue.ACTION (fn () => i),p1,p2))
fun ERROR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(
ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(
ParserData.MlyValue.VOID,p1,p2))
end
end
