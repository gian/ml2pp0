signature LTS =
sig
  type state  
  eqtype 'l transition
  type 'l lts (* An LTS is parameterised on the type of the label *)

  exception NonDeterminism of string
  exception CannotPerform of string * state

  val empty : 'l lts

  (* LTS -> source -> label -> dest -> LTS' *)
  val add_transition : 'l lts -> 'l transition -> 'l lts
  val get_transition : ''l lts -> state -> ''l -> (''l transition) list

  val new_state : unit -> state
  val last_state : unit -> state

  val get_src : 'l transition -> state
  val get_dest : 'l transition -> state
  
  val visit : state -> unit

  val get_outgoing : 'l lts -> state -> ('l transition) list

  val toString : 'l lts -> ('l -> string) -> string
  val toDot : (int * string * int) list -> string

  (* LTS Behavioural Checking *)
  val can_perform : (int * string * int) list -> string list -> bool
  val can_perform_anywhere : (int * string * int) list -> string list -> bool
  
  val print_visited : unit -> unit
  val print_unvisited : string lts -> unit
  val get_visited : unit -> state Set.set
  val get_unvisited : string lts -> state Set.set
  val reset_visited : unit -> unit
end

structure Lts : LTS =
struct
  type state = int
  type 'l transition = state * 'l * state
  type 'l lts = ('l transition) list

  val empty = []

  val state_count = ref 0
  fun new_state () = (state_count := (!state_count) + 1; !state_count)
  fun last_state () = (!state_count)
 
  val visitedSet : state Set.set ref = ref (Set.empty) 

  fun visit t = 
	let
		val _ = Debug.print_dbg ("VISIT: " ^ Int.toString t ^ "\n")
	in
		visitedSet := Set.insert(t, !visitedSet) 
	end
  fun get_visited () = !visitedSet

  fun get_unvisited lts = 
    let
        fun buildNodeList [] s = s
          | buildNodeList ((_,"SKIP",_)::t) s = buildNodeList t s
          | buildNodeList ((s1,_,s2)::t) s = buildNodeList t (Set.insert(s1,Set.insert(s2,s)))
    in
	Set.diff(buildNodeList lts Set.empty,!visitedSet)
    end

  fun reset_visited () = visitedSet := Set.empty 

  exception NonDeterminism of string
  exception CannotPerform of string * state


  fun get_outgoing l s = List.filter (fn (s1,_,_) => s1 = s) l
  
  fun add_transition l t = l @ [t]
  fun get_transition l s lab = List.filter (fn (_,lab',_) => lab' = lab) (get_outgoing l s)
 
 
  fun get_src (s,_,_) = s
  fun get_dest (_,_,s) = s

  fun toString [] _ = "\n"
    | toString ((src,l,dst)::t) pr = "" ^ (Int.toString src) ^ " --" ^ (pr l) ^ "--> " ^ (Int.toString dst) ^ "\n" ^ toString t pr
  
  fun node_list_to_string l = String.concatWith ", " (List.map Int.toString l)

  fun print_visited () = Debug.print_dbg ("VISITED: \n" ^ node_list_to_string (!visitedSet))
  fun print_unvisited lts = Debug.print_dbg ("UNVISITED: \n" ^ node_list_to_string(get_unvisited lts))

  fun toDot l =
      let
         fun trans [] = "\n"
           | trans ((src,l,dst)::t) = "  n" ^ Int.toString src ^ " ->  n" ^ Int.toString dst ^ " [label=\"" ^ l ^ "\"];\n" ^ trans t
         fun nodes n m = if n > m then "\n" else "n" ^ Int.toString n ^ " [style=invis,height=0.1,width=0.1,fixedsize=true];\n" ^ nodes (n+1) m
      in
         "digraph lts {\n" ^ trans l ^ (nodes 0 (last_state())) ^ "\n}\n"
      end

  fun perform_step 0 lts s h = raise (Fail "Exhausted iterations")
    | perform_step itr lts s "_" =
      let
	 val _ = visit s
         val skips = get_outgoing lts s
         val _ = if length skips = 0 then raise (CannotPerform ("_",s)) else ()
      in
         if length skips = 1 then get_dest (hd skips) else raise (Fail "Non-determinism in wildcards is not implemented yet")                
      end
    | perform_step itr lts s h = 
      let
	 val _ = visit s
         val ns = get_transition lts s h
         val _ = if length ns > 1 
                  then raise (NonDeterminism("In state "^Int.toString s^" there are "^Int.toString(length ns)^" transitions with label " ^ h)) 
                  else ()
      in if length ns = 1 then get_dest (hd ns)
         else 
          let
           val skips = get_transition lts s "SKIP"
           val _ = if length skips = 0 then raise (CannotPerform (h,s)) else ()
           fun untilFound [] = ~1
             | untilFound (ss::st) = 
               let
                  val itr' = itr - 1
                  val cand = perform_step itr' lts ss h handle (CannotPerform _) => ~1
               in
                  if cand >= 0 then cand else untilFound st
               end 
          in
            untilFound (map get_dest skips)                 
          end
      end
  fun can_perform_frag_h lts ~1 _ = false
    | can_perform_frag_h lts s [] = true
    | can_perform_frag_h lts s (h::t) =
      let
         val s' = perform_step 5000 lts s h 
      in
         can_perform_frag_h lts s' t
      end handle e => false

  fun at_end lts ~1 = false
    | at_end lts s = if length (get_outgoing lts s) = 0 then true
                        else 
                         let
                            val skips = get_transition lts s "SKIP"
                         in
                            if length skips = 1 then at_end lts (get_dest (hd skips)) else false
                         end

  fun can_perform_h lts ~1 _ = false
    | can_perform_h lts s [] = true
    | can_perform_h lts s ["*NONTERM*"] = true
    | can_perform_h lts s [last] = 
      let
         val s' = perform_step 5000 lts s last
      in
         if s' <> ~1 andalso (at_end lts s') then true else 
             (raise (Fail ("incomplete trace at: " ^ last)))
      end 
    | can_perform_h lts s (h::t) =
      let
         val s' = perform_step 5000 lts s h 
      in
         (can_perform_h lts s' t)
      end handle (Fail x) => raise (Fail x) | e => false

  fun can_perform lts [] = (true)
    | can_perform lts trace = can_perform_h lts 0 trace

  fun can_perform_anywhere lts trace =
    let
       val max = last_state ()
       fun doN 0 = can_perform_frag_h lts 0 trace
         | doN n = can_perform_frag_h lts n trace orelse doN (n-1)
    in
       doN max
    end

end

