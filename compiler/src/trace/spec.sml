structure Spec =
struct

  datatype action = Wildcard
                | Label of string
                | Write of string * string
                | Read of string * string
                | NonTerm

  fun parse_action x = Label x 

  type spec = {operations : action list, necessary : action SpecBuilder.trace_element SpecBuilder.trace list, safe : action SpecBuilder.trace_element SpecBuilder.trace list, forbidden : action SpecBuilder.trace_element SpecBuilder.trace list} 

  fun actionToString Wildcard = "_"
    | actionToString (Label s) = s
    | actionToString (Write (s1,s2)) = s1 ^ "!" ^ s2 
    | actionToString (Read (s1,s2)) = s1 ^ "?" ^ s2
    | actionToString NonTerm = "*NONTERM*" 

  fun pplts x = Lts.toString x actionToString 

  fun ppops x = String.concatWith "\n" (map actionToString x)

  fun pptraces x = String.concatWith "\n" (map (SpecBuilder.traceToString actionToString) x) 

  fun ppstrtrace x = String.concatWith ", " x

  fun spec2tex (s:spec) filename =
      let
           val out = "\\documentclass[a4paper]{article}\n\\usepackage{fancyvrb}\n\\usepackage{pst-node}\n\n\\begin{document}\n" ^
                 "\\begin{figure}[T]\n" ^
                 "\\begin{Verbatim}[frame=single,label={Operations},framesep=5mm,labelposition=topline]\n" ^
		 (ppops (#operations s)) ^ "\n" ^ "\\end{Verbatim}\n" ^
                 "\\begin{Verbatim}[frame=single,label={Necessary},framesep=5mm,labelposition=topline]\n" ^
		 (pptraces (#necessary s)) ^ "\n" ^ "\\end{Verbatim}\n" ^
                 "\\begin{Verbatim}[frame=single,label={Safe},framesep=5mm,labelposition=topline]\n" ^
		 (pptraces (#safe s)) ^ "\n" ^"\\end{Verbatim}\n" ^
		 "\\begin{Verbatim}[frame=single,label={Forbidden},framesep=5mm,labelposition=topline]\n" ^
		 (pptraces (#forbidden s)) ^
		 "\\end{Verbatim}\n\\end{figure}\n\\end{document}\n"
           val f = TextIO.openOut filename
           val _ = TextIO.output (f, out)
           val _ = TextIO.closeOut f
	in
           Debug.print_dbg out 
	end

  fun spec2string (s:spec) =
                 "OPERATIONS\n" ^
		 (ppops (#operations s)) ^ "\n" ^
                 "NECESSARY\n" ^
		 (pptraces (#necessary s)) ^ "\n" ^
                 "SAFE\n" ^ 
		 (pptraces (#safe s)) ^ "\n" ^
                 "FORBIDDEN\n" ^
		 (pptraces (#forbidden s))
     

  fun stripact (Label x) = x 
    | stripact Wildcard = "_"
    | stripact (Read (s1,s2)) = s1 ^ "?" ^ s2
    | stripact (Write (s1,s2)) = s1 ^ "!" ^ s2
    | stripact NonTerm = "*NONTERM*"

  exception Unsatisfied of string * string list

  fun check lts (spec:spec) =
      let
	 val necessary = List.map (fn x => List.map stripact x) (SpecBuilder.prefixClosedTraces NonTerm (#necessary spec))
         val _ = Lts.reset_visited ()
         val necessaryCheck = if necessary = [] then true else not (List.all (fn x => not (Lts.can_perform lts x)) necessary)
	 val _ = Lts.print_unvisited (List.filter (fn (_,SKIP,_) => false | _ => true) lts) 
         val _ = if not necessaryCheck then raise (Unsatisfied ("liveness-necessary",hd (List.filter (fn x => not (Lts.can_perform lts x)) necessary))) else ()
	 val _ = if necessary = [] orelse Lts.get_unvisited lts = [] then true else (raise (Unsatisfied ("safety-necessary", 
			List.map (fn (_,l,_) => l) (Lts.get_outgoing lts (hd (Lts.get_unvisited lts)))))) 


         val safe = List.map (fn x => List.map stripact x) (SpecBuilder.prefixClosedTraces NonTerm (#safe spec))
         val _ = Debug.print_dbg ("SAFE WITH NONTERM:\n") 
         fun prstrt x = Debug.print_dbg ((ppstrtrace x) ^ "\n")
         val _ = List.app prstrt safe
         val forbidden = List.map (fn x => List.map stripact x) (SpecBuilder.prefixClosedTraces NonTerm (#forbidden spec))
         val safeCheck = if safe = [] then true else not (List.all (fn x => not (Lts.can_perform lts x)) safe)
         val _ = if not safeCheck then raise (Unsatisfied ("liveness",hd (List.filter (fn x => not (Lts.can_perform lts x)) safe))) else ()
         val forbiddenCheck = List.all (fn x => if not (Lts.can_perform_anywhere lts x) then true else raise Unsatisfied("forbidden",x)) forbidden
         val _ = if not forbiddenCheck then raise (Unsatisfied ("safety",[])) else ()
         
	       in
         (safeCheck,forbiddenCheck)
      end handle (Unsatisfied (loc,tr)) => (print ("ERROR: " ^ loc ^ " violated.  Offending trace follows:\n" ^ ppstrtrace tr ^ "\n");(false,false))

end
