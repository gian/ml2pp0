structure Behav =
struct
   structure L = Lts
   open TypedAST
   structure A = Absyn
   structure T = Types

   exception InvalidAst of string * typed ast

   val env = ref [] : (string * typed ast) list ref

   fun btApply (BTUnapplied x) = x
     | btApply x = x

   fun simplify BTSkip = BTSkip
     | simplify (BTSeq (BTSkip,b)) = simplify b
     | simplify (BTSeq (b,BTSkip)) = simplify b
     | simplify (BTSeq (b1,b2)) = BTSeq (simplify b1, simplify b2)
     | simplify (BTChoice (b1,b2)) = BTChoice (simplify b1, simplify b2)
     | simplify (BTUnapplied _) = BTSkip
     | simplify (BTCompose (b1,b2)) = BTCompose (simplify b1, simplify b2)
     | simplify (BTSend (b,t)) = BTSend (simplify b, t)
     | simplify (BTRecv (b,t)) = BTRecv (simplify b, t)
     | simplify (BTStar b) = BTStar (simplify b)
     | simplify BTFinal = BTFinal
     | simplify (BTIdentifier x) = BTIdentifier x

   (*XXX: This does a terrible job of avoiding variable capture *)
   fun occursin s t (Leaf (Var s', t')) = s = s' andalso t = t'
     | occursin s t (Leaf _) = false
     | occursin s t (Node (_, [])) = false
     | occursin s t (Node (k, (h::tr))) = occursin s t h orelse occursin s t (Node (k, tr))
 
   fun astNodeToBtype (BinOp k) t [c1,c2] = A.BTSeq (astToBtype c1, astToBtype c2)
     | astNodeToBtype If t [c1,c2,c3] = A.BTSeq (astToBtype c1, BTChoice (astToBtype c2, astToBtype c3))
     | astNodeToBtype (Let s) t [c1,c2] = A.BTSeq (astToBtype c1, astToBtype c2)
     | astNodeToBtype Seq t [c1,c2] = A.BTSeq (astToBtype c1, astToBtype c2)
     | astNodeToBtype App t [c1,c2] = A.BTSeq (astToBtype c2, btApply (astToBtype c1)) (* This is backwards because of eager evaluation *)
     | astNodeToBtype AnonFn t [c1,c2] = BTUnapplied (astToBtype c2)
     | astNodeToBtype (ValBinding s) (TyArrow t) [c1] = 
       let
          val b1 = astToBtype c1
          val _ = Types.insertBe (A.LVar s) b1
          val _ = Debug.print_dbg ("INSERTBE: " ^ s ^ " as " ^ A.ppbehavty (btApply b1) ^ "\n")
          val b1' = if (occursin s (TyArrow t) c1) then (BTStar (btApply b1)) else b1
       in
          b1'
       end 
     | astNodeToBtype (ValBinding s) t [c1] = 
       let
          val b1 = astToBtype c1
          val _ = Debug.print_dbg ("VALBINDING: " ^ s ^ " as " ^ A.ppbehavty (btApply b1) ^ "\n")
          val _ = Types.insertBe (A.LVar s) b1
          val _ = Debug.print_dbg ("INSERTBE: " ^ s ^ " as " ^ A.ppbehavty (btApply b1) ^ "\n")
       in
          b1
       end (* Need second clause with check for s occuring in c1 (recursion) *)
     | astNodeToBtype opr t x = raise (InvalidAst ("AST node is invalid.  Possible compiler bug?", Node((opr,t),x)))
 

   and astToBtype (Leaf (Var s, TyArrow _)) = Types.lookupBe (A.LVar s)
     | astToBtype (Leaf (Var s, _)) = A.BTSkip
     | astToBtype (Leaf _) = A.BTSkip
     | astToBtype (Node ((opr,t),ch)) = astNodeToBtype opr t ch
 
   fun astListToBtype [] = A.BTFinal
     | astListToBtype (h::t) = A.BTSeq (astToBtype h, astListToBtype t)  handle (InvalidAst (m,x)) => (raise (Fail ("AST: " ^ pptypedast_h x)))

   fun btypeToLts_h lts src (BTSeq (b1,b2)) =
       let
         val lts' = btypeToLts_h lts src b1
         val lts'' = btypeToLts_h lts' (L.last_state ()) b2
       in
         lts''
       end
     | btypeToLts_h lts src (BTChoice (b1,b2)) =
       let
         val lts' = btypeToLts_h lts src b1
         val lts'' = btypeToLts_h lts' src b2
       in
         lts''
       end 
     | btypeToLts_h lts src BTFinal = lts
     | btypeToLts_h lts src (BTSend(b,t)) =
       let
         val nxt = L.new_state ()
         val tr = (src,A.ppbehavty (BTSend (b,t)),nxt)
       in
         L.add_transition lts tr
       end
     | btypeToLts_h lts src (BTRecv(b,t)) =
       let
         val nxt = L.new_state ()
         val tr = (src,A.ppbehavty (BTRecv (b,t)),nxt)
       in
         L.add_transition lts tr
       end
     | btypeToLts_h lts src BTSkip =
       let
          val nxt = L.new_state ()
          val tr = (src,"SKIP",nxt)
       in
          L.add_transition lts tr
       end
     | btypeToLts_h lts src (BTStar b) =
       let
          val lts' = btypeToLts_h lts src b
       in
          L.add_transition lts' (L.last_state(),"SKIP",src)
       end
     | btypeToLts_h lts src x = raise (Fail ("Unhandled case for Behavioural Type to LTS conversion: " ^ A.ppbehavty x ^ "\n"))

   fun btypeToLts b = btypeToLts_h L.empty 0 b
   
   fun strip_fn (Node ((AnonFn,_), [c1,c2])) = c2
     | strip_fn x = x

   fun printScopedEnv scopedEnv = Debug.print_dbg ("ScopedEnv: " ^ (String.concatWith "," (List.map (fn (x,y) => x ^ " = " ^ Int.toString y) scopedEnv)) ^ "\n")
   fun astToLts lts src scopedEnv (Leaf _) = [(src,"SKIP",L.new_state())]
     | astToLts lts src scopedEnv (Node ((Seq,t),[c1,c2])) = 
       let
          val trc1 = astToLts lts src scopedEnv c1
       in
          trc1 @ (astToLts lts (Lts.last_state ()) scopedEnv c2)
       end
     | astToLts lts src scopedEnv (Node ((App,t),[c1,c2])) = 
       (case c1 of (Leaf(Var s,_)) =>
       let
           val _ = Debug.print_dbg ("APP VAR: " ^ s ^ "\n")
           val _ = printScopedEnv scopedEnv
           val trc2 = astToLts lts src scopedEnv c2
       in if T.contains_h s scopedEnv 
           then trc2 @ [(L.last_state(),"SKIP",T.lookup_h s scopedEnv)]
           else 
             if T.containsBe (LVar s)
               then 
                 trc2 @ [(L.last_state(),A.ppbehavty (T.lookupBe (LVar s)),L.new_state())]
               else
                 let
                     val scopedEnv' = (s,L.last_state()) :: scopedEnv
                 in
                   trc2 @ (astToLts lts (L.last_state()) scopedEnv' ((T.lookup_h s (!env)))) handle Fail _ => 
                    (raise Fail ("Failed at scoping of " ^ s ^ "\n" ^ "ScopedEnv: " ^ (String.concatWith "," (List.map (fn (x,y) => x ^ " = " ^ Int.toString y) scopedEnv') ^ "\n")); [])
                 end
       end    
               | (Node((AnonFn,t),[cc1,cc2])) => astToLts lts (L.last_state()) scopedEnv cc2
               | _ => raise (Fail "Application that I don't understand has occurred\n"))
     | astToLts lts src scopedEnv (Node ((ValBinding s,TyArrow _),[c1])) = 
       let
          val _ = (env := (s,c1) :: (!env))
       in
          [] 
       end
     | astToLts lts src scopedEnv (Node ((ValBinding s,_),[c1])) = 
       let
          val scopedEnv' = (s,src) :: scopedEnv
       in
          astToLts lts src scopedEnv' c1
       end
     | astToLts lts src scopedEnv (Node ((AnonFn,t),[v,c1])) = astToLts lts src scopedEnv c1
     | astToLts lts src scopedEnv (Node ((Let k,t),[c1,c2])) =
       let
          val trc1 = astToLts lts src scopedEnv c1
          val scopedEnv' = (k,L.last_state()) :: scopedEnv
       in
          trc1 @ (astToLts lts (L.last_state()) scopedEnv' c2)
       end
     | astToLts lts src scopedEnv (Node ((If,t),[c1,c2,c3])) = 
       let
          val trc1 = astToLts lts src scopedEnv c1
          val trmst1 = L.last_state ()
          val trc2 = astToLts lts trmst1 scopedEnv c2
          val trmst2 = L.last_state () (* Terminating state of the "true" branch *)
          val trc3 = astToLts lts trmst1 scopedEnv c3
          val trmst3 = L.last_state () (* Terminating state of the "false" branch *)
          val d = L.new_state ()

          val _ = Debug.print_dbg ("IF CALC: trimst1: " ^ Int.toString trmst1 ^ " trmst2: " ^ Int.toString trmst2 ^ " trmst3: " ^ Int.toString trmst3 ^ " d: " ^ Int.toString d ^ "\n")
       in
          trc1 @ trc2 @ trc3 @ [(trmst2,"SKIP",d)] @ [(trmst3,"SKIP",d)]
       end
     | astToLts lts src scopedEnv (Node ((BinOp x,t),[c1,c2])) =
          (astToLts lts src scopedEnv c1) @ (astToLts lts (L.last_state()) scopedEnv c2)
     | astToLts lts src scopedEnv x =
       let
          val _ = Debug.print_dbg "ASTTOLTS UNRECOGNISED AST:\n"
          val _ = Debug.print_dbg ("LTS:\n" ^ (L.toString lts (fn x => x)) ^ "\n")
          val _ = Debug.print_dbg ("SRC:\n" ^ (Int.toString src) ^ "\n")
          val _ = Debug.print_dbg ("ScopedEnv:\n")
          val _ = List.app (fn (x,y) => Debug.print_dbg (x ^ " = " ^ Int.toString y ^ "\n")) scopedEnv
          val _ = Debug.print_dbg ("AST:\n" ^ TypedAST.pptypedast_h x ^ "\n")
       in
          []
       end
        
   fun btype (filename) = 
      let 
         val (ast,c) = Types.stype (Parse.parse filename)
         (*val bt = simplify (simplify (astListToBtype ast))
         val _ = Debug.print_dbg ("BENV:\n" ^ Types.ppbenv (#be (!Types.env)) ^ "\n")
         val blts = btypeToLts bt*)

         fun aToL lts [] = lts
           | aToL lts (h::t) = let
               val _ = Debug.print_dbg ("Term: " ^ pptypedast_h h ^ "\nPrevLTS:\n" ^ (L.toString lts (fn x => x)) ^ "\n")
               val _ = Debug.print_dbg ("ENV:\n")
               val _ = List.app (fn (x,y) => Debug.print_dbg (x ^ " = " ^ pptypedast_h y ^ "\n")) (!env)
               val lts' = astToLts lts (L.last_state()) [] h
             in
                 aToL (lts @ lts') t
             end
         
         val blts = aToL L.empty ast

         val _ = Debug.print_dbg ("BLTS:\n" ^ (L.toString blts (fn x => x)) ^ "\n")
         val _ = Debug.print_dbg ("DOT\n\n" ^ L.toDot blts)
	 val dotFile = TextIO.openOut (filename ^ ".dot")
	 val _ = TextIO.output(dotFile, (L.toDot blts) ^ "\n")
	 val _ = TextIO.closeOut dotFile
      in
         blts 
      end
 
end
