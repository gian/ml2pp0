(* Construct a LTS from a set of traces *)
structure SpecBuilder =
struct
  open Lts

  datatype trace_modifier = Star | NonTerm

  type 't trace = 't list
  type 't trace_element = 't * trace_modifier option
  
  fun add_trace lts s [] = lts
    | add_trace lts s ((h,NONE)::t) = 
      if get_transition lts s h = [] 
        then 
          let 
            val s' = new_state ()
            val lts' = add_transition lts (s,h,s')
          in
            add_trace lts' s' t
          end
        else
          add_trace lts (get_dest (hd (get_transition lts s h))) t
    | add_trace lts s ((h,SOME Star)::t) =
        add_trace (add_transition lts (s,h,s)) s t (* Add a self-loop with label h *)
     
  fun buildLTS_h [] lts = lts
    | buildLTS_h (h::t) lts = 
      let
         val lts' = add_trace lts 0 h
      in
         buildLTS_h t lts'
      end

  fun buildLTS k = buildLTS_h k Lts.empty

  fun traceElementToString pr (x,SOME Star) = pr x ^ "*"
    | traceElementToString pr (x,SOME NonTerm) = "*NONTERM*"
    | traceElementToString pr (x,NONE) = pr x

  fun traceToString pr t  = String.concatWith ", " (map (traceElementToString pr) t)

  fun prefixClosedTrace nt limit [] = []
    | prefixClosedTrace nt (limit:int) (((te,NONE) :: t) : 't trace_element trace) = te :: prefixClosedTrace nt limit t
    | prefixClosedTrace nt limit ((te,SOME Star) :: t) = 
      let
         fun doN x 0 = []
           | doN x n = x :: doN x (n-1)
      in
         (doN te limit) @ (prefixClosedTrace nt limit t)
      end
    | prefixClosedTrace nt limit ((te,SOME NonTerm) :: t) = nt :: prefixClosedTrace nt limit t

  fun prefixClosedTraces_h nt [] = []
    | prefixClosedTraces_h nt tr =
      let
         val tr' = (case (List.last tr) of (x,SOME Star) => tr @ [(x,SOME NonTerm)]
                                         | _ => tr)
         fun doN f n m = if n > m then [] else (f n tr') :: (doN f (n+1) m)
      in
         doN (prefixClosedTrace nt) 0 30
      end 


  fun prefixClosedTraces nt [] = []
    | prefixClosedTraces nt (h::t) = prefixClosedTraces_h nt h @ prefixClosedTraces nt t
end


