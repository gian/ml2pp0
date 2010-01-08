(*
 ************************************************************************
 *		Turing-machine emulation in a good-lookin' ML
 *
 * states are integers 0 - ...; some special states are labeled with
 * negative numbers: whenever one such state occurs, the machine stops
 * and returns its current status.
 *
 * The status of the Turing machine is a 4-ple
 *   (state, left_part, curr_char, right_part)
 *
 * A Turing_program (transition-function) is a list of transition_rules,
 * each having the form
 *	(curr_state,curr_symbol,new_state,new_symbol)
 * where 'new_symbol' may be any symbol of the alphabet plus Move_left and 
 * Move_right
 *)

type State = int;
val halt_state = ~1;			(* Halt				*)
val hang_state = ~2;			(* Moving past the left end	*)
val badprogram_state = ~3;		(* Not all transitions defined  *)

type Symbol = string;
val  Move_left  = "*LEFT*";		(* Special symbols *)
val  Move_right = "*RIGHT*";
val  Blank      = "#";

	     (* old   Left part    Current   Right part		*)
type Status = State * Symbol list * Symbol * Symbol list;

		     (* Curr   Curr     Next     Next		*)	
type Transition_rule = State * Symbol * State * Symbol;

			(* Takes an initial status and a Turing program   *)
			(* and returns the status when the machine stops  *)
fun turing_machine((cstate,leftp,csymbol,rightp),program) =
	let
				(* Returns (new_state,new_symbol) depending *)
				(* on the current status		    *)
	fun get_new_statesymbol(cstate,csymbol,[]) = 
		(badprogram_state,"*BADPROGRAM*") |
	    get_new_statesymbol(cstate,csymbol,
				(tstate,tsymbol,tnewstate,tnewsymbol)::tt) = 
	    	if cstate = tstate andalso csymbol = tsymbol then
		   (tnewstate,tnewsymbol)
		else get_new_statesymbol(cstate,csymbol,tt)

				(* Chop off the last symbol of the list	    *)
				(* and return (chopped-list,chopped-symbol) *)
	and get_last (prl,[x])  = (prl,x) |
	    get_last(prl,h::t) = get_last(prl@[h],t)

				(* Move left				*)
	and move_left(newstate,[]) = (hang_state,[],csymbol,rightp) |
	    move_left(newstate,leftp) = 
		let
		val (newl,newsymbol) = get_last([],leftp)
		in
		    turing_machine((newstate,newl,newsymbol,csymbol::rightp),
			           program)
		end
	and move_right(newstate,[]) =
		turing_machine((newstate,leftp@[csymbol],Blank,[]),
			       program) |
	    move_right(newstate,rs::rt) =
		turing_machine((newstate,leftp@[csymbol],rs,rt),
			       program)
	in
	    if cstate < 0 then (cstate,leftp,csymbol,rightp)
	    else
	    let
	    val (newstate,newsymbol) = 
		get_new_statesymbol(cstate,csymbol,program)
	    in
		if      newsymbol = Move_left  then move_left(newstate,leftp)
		else if newsymbol = Move_right then move_right(newstate,rightp)
		else    
			turing_machine((newstate,leftp,newsymbol,rightp),
				       program)
	    end
	end;

				(* Example 1				*)
				(* The successor function		*)
val prog_succ = [
	(0,"I",halt_state,Move_right),
	(0,"#",0,"I")
];

val _ = turing_machine((0,["#","I","I","I","I"],"#",[]),prog_succ);


				(* Example 2				*)
				(* Replacing each occurrence of a by b	*)
				(* and vice versa			*)
val prog1 = [
	(0,"a",1,Move_left),
	(0,"b",1,Move_left),
	(0,"#",1,Move_left),
	(1,"a",0,"b"),
	(1,"b",0,"a"),
	(1,"#",2,Move_right),
	(2,"a",2,Move_right),
	(2,"b",2,Move_right),
	(2,"#",halt_state,"#")
];
	
val _ = turing_machine((0,["#","a","a","b","a","a","b"],"#",[]),prog1);

				(* Example 3				*)
				(* Decision machine			*)
				(* Decide whether the no of chars in the*)
				(* string even or odd			*)

val prog_decision = [
	(0,"#",1,Move_left),
	(1,"a",2,"#"),
	(1,"#",4,Move_right),
	(2,"#",3,Move_left),
	(3,"a",0,"#"),
	(3,"#",6,Move_right),
	(4,"#",5,"Yes"),
	(5,"Yes",halt_state,Move_right),
	(5,"No",halt_state,Move_right),
	(6,"#",5,"No")
];

val _ = turing_machine((0,["#","a","a","a","a","a","a"],"#",[]),prog_decision);
val _ = turing_machine((0,["#","a","a","a","a","a"],"#",[]),prog_decision);

