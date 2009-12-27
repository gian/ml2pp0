structure Types =
struct
   open Absyn
   structure T = TypedAST

   type env = { ty : (ty * ty) list, va : (ty * ty) list, be : (ty * behavty) list }
   val env = ref {ty=[],va=[],be=[]} : env ref

   val environments = ref [] : env list ref

   val globalTypedAst = ref [] : T.typed T.ast list ref

   val fresh = ref 0

   fun mkFresh () = (fresh := 1 + !fresh ; !fresh)
  
   fun pushEnv () = environments := ((!env) :: (!environments))

   fun popEnv () = (env := hd (!environments); environments := tl (!environments))

   val remappings = ref [] : (ty * ty) list list ref
   val remapping = ref [] : (ty * ty) list ref

   fun pushRemapping () = remappings := ((!remapping) :: (!remappings))
   fun popRemapping () = (remapping := hd (!remappings); remappings := tl (!remappings))

   fun insertTy t1 t2 = env := {ty=(t1,t2)::(#ty (!env)), va = (#va (!env)), be = (#be (!env))}
   fun insertVal t1 t2 = env := {ty=(#ty (!env)), va = (t1,t2)::(#va (!env)), be = (#be (!env))}
   fun insertBe t1 t2 = env := {ty=(#ty (!env)),va = (#va (!env)),be = (t1,t2)::(#be (!env))}
   fun lookup_h ty [] = raise (Fail ("ERROR: Could not find binding"))
     | lookup_h ty ((k,v)::t) = if ty = k then v else lookup_h ty t
   fun lookupTy t1 = lookup_h t1 (#ty (!env))
   fun lookupVal t1 = lookup_h t1 (#va (!env)) handle (Fail m) => raise (Fail (m ^ " for var " ^ ppty t1))
   fun lookupBe t1 = lookup_h t1 (#be (!env)) handle _ => BTSkip
   fun contains_h ty [] = false
     | contains_h ty ((k,_)::t) = if ty = k then true else contains_h ty t
   fun containsTy t1 = contains_h t1 (#ty (!env))
   fun containsVal t1 = contains_h t1 (#va (!env))
   fun containsBe t1 = contains_h t1 (#be (!env))

   (* Pull in action names and types for the language "built in" environment *)
   (*XXX: This is very fragile.  Needs to be replaced by a more robust solution *)
   fun loadTopLevel filename =
     let
        fun clean s = String.implode (List.filter (fn #"\n" => false | #" " => false | _ => true) (String.explode s))

        val fp = TextIO.openIn filename
        fun readRecord fp = 
          let
             val empty = {name="",inty="",outty="",chan="",action=""}
	     fun process [name,t1,t2,ch,si] = {name=name,inty=t1,outty=t2,chan=ch,action=si}
               | process _ = empty

             val l = TextIO.inputLine fp
	     val fields = String.fields (fn #"\t" => true | _ => false) (clean (valOf l))
             val d = if String.isPrefix "#" (valOf l) orelse (valOf l) = "\n" then readRecord fp else process fields
          in
             if d <> empty then d else readRecord fp 
          end 

        fun insertRecord r = (insertVal (LVar (#name r)) (TyArrow (TyName (#inty r), TyName (#outty r))) ;
                              insertBe  (LVar (#name r)) ((BTSend(BTIdentifier(#chan r,SOME (TyName "channel")),SOME (TyName (#action r))))))

	fun readAll fp l = let val k = readRecord fp in if (#name k) = "" then l else (readAll fp (k :: l)) end handle Option => l
     in
           (app insertRecord (readAll fp []); TextIO.closeIn fp; true)
     end handle IOException => false

   val r = loadTopLevel "toplevel.conf"
   val r' = r orelse (loadTopLevel "conf/toplevel.conf")
   val r'' = r' orelse (loadTopLevel "../conf/toplevel.conf")
   val r''' = r'' orelse (loadTopLevel "/usr/share/tracespec/toplevel.conf")

   val _ = if r''' then () else (print "WARNING: Could not load top level configuration\n")

   (* Set up the top level environment *)
   val _ = insertVal (LVar "print") (TyArrow (TyName "string",TyName "unit"))
   val _ = insertBe  (LVar "print") ((BTSend(BTIdentifier("io",SOME (TyName "channel")),SOME (TyName "print"))))
   val _ = insertVal (LVar "open") (TyArrow (TyName "string", TyName "filehandle")) 
   val _ = insertBe  (LVar "open") ((BTSend(BTIdentifier("file",SOME (TyName "channel")),SOME (TyName "open"))))
   val _ = insertVal (LVar "read") (TyArrow (TyName "filehandle", TyName "string")) 
   val _ = insertBe  (LVar "read") ((BTSend(BTIdentifier("file",SOME (TyName "channel")),SOME (TyName "read"))))
   val _ = insertVal (LVar "close") (TyArrow (TyName "filehandle",TyName "unit"))
   val _ = insertBe  (LVar "close") ((BTSend(BTIdentifier("file",SOME (TyName "channel")),SOME (TyName "close"))))
   val _ = insertVal (LVar "feof")  (TyArrow (TyName "filehandle", TyName "bool"))
   val _ = insertBe  (LVar "feof")  (BTSkip)

   fun isval (Integer _) = true
     | isval (String s) = true
     | isval (AnonFn _) = true
     | isval (Nil) = true
     | isval (Unit) = true
     | isval (UMinus x) = isval x
     | isval (BinOp (x,y,z)) = isval x andalso isval z
     | isval (BNot e) = isval e
     | isval (True) = true
     | isval (False) = true
     | isval x = false

   fun ppenv1 (e1,e2) = ppty e1 ^ " : " ^ ppty e2 ^ "\n"

   fun ppenv [] = ""
     | ppenv (h::t) = ppenv1 h ^ ppenv t 

   fun ppbenv1 (e1,e2) = ppty e1 ^ " : " ^ ppbehavty e2 ^ "\n"

   fun ppbenv [] = ""
     | ppbenv (h::t) = ppbenv1 h ^ ppbenv t 

   fun instTerm (TyPoly x) constr =
       let
           val n1 = if contains_h (TyPoly x) (!remapping) 
                    then let
                            val p = lookup_h (TyPoly x) (!remapping)
                            val constr' = substinconstr (TyPoly x) p constr
                         in
                            (p,constr')
                         end
                    else let
                            val p = TyVar (mkFresh ())
                            val _ = (remapping := (TyPoly x,p)::(!remapping))
                            val constr' = substinconstr (TyPoly x) p constr
                         in
                            (p,constr')
                         end
       in
           n1
       end
     | instTerm (TyArrow (x,y)) constr = 
       let
           val (n1,constr') = instTerm x constr
           val (n2,constr'') = instTerm y constr'
           val _ = Debug.print_dbg ("Instantiated term TyArrow(" ^ ppty x ^ "," ^ ppty y ^ ") to TyArrow(" ^ ppty n1 ^ "," ^ ppty n2 ^ ")\n")
       in
           (TyArrow(n1,n2),constr'')
       end
     | instTerm x constr = (x,constr)
 
   and constrain_e (Integer _) = (T.Leaf (T.Integer,TyName "int"), TyName "int", [])
     | constrain_e (String _) = (T.Leaf (T.String,TyName "string"), TyName "string", [])
     | constrain_e (AnonFn []) = raise (Fail "Empty function clause")
     | constrain_e (AnonFn (((Var (e1,_)),e2)::t)) = 
       let
          val tx = TyVar (mkFresh ())
          val _ = insertVal (LVar e1) tx
          val (a2,t2,c2) = constrain_e e2
          val _ = Debug.print_dbg ("ANONCONSTR: " ^ ppenv c2 ^ "\n")
       in
          (T.Node ((T.AnonFn, TyArrow(tx,t2)), [T.Leaf (T.Var e1,tx),a2]), TyArrow(tx,t2), c2)
       end
     | constrain_e (Nil) = (T.Leaf (T.Nil, TyNil), TyCon (TyVar (mkFresh ()), TyName "list"), [])
     | constrain_e (Unit) = (T.Leaf (T.Unit, TyName "unit"), TyName "unit",[])
     | constrain_e (Var (s,NONE)) = 
       let
          val p = lookupVal (LVar s)
       in
          (T.Leaf(T.Var s,p), p, [])
       end
     | constrain_e (Var (s,t)) = raise (Fail "Case not handled")
     | constrain_e (App (e1, e2)) = 
       let
          val _ = pushRemapping ()
          val (a1,t1',c1') = constrain_e e1
          val (t1,c1) = instTerm t1' c1'
          val (a2,t2,c2) = (constrain_e e2)
          val tx = TyVar (mkFresh ())
          val newconstr = [(t1,TyArrow(t2,tx))]
          val _ = Debug.print_dbg ("APP: " ^ ppty t1 ^ " to " ^ ppty t2 ^ "\n")
          val _ = popRemapping ()
       in
          (T.Node ((T.App,tx), [a1,a2]), tx, newconstr @ c1 @ c2)
       end
     | constrain_e (BinOp (e1, Plus, e2)) =
       let
          val (a1,t1,c1) = constrain_e e1
          val (a2,t2,c2) = constrain_e e2
          val newconstr = [(t1,TyName "int"), (t2, TyName "int")]
       in
          (T.Node ((T.BinOp Plus,TyName "int"), [a1, a2]), TyName "int", newconstr @ c1 @ c2)
       end
     | constrain_e (BinOp (e1, Minus, e2)) =
       let
          val (a1,t1,c1) = constrain_e e1
          val (a2,t2,c2) = constrain_e e2
          val newconstr = [(t1,TyName "int"), (t2, TyName "int")]
       in
          (T.Node ((T.BinOp Minus,TyName "int"), [a1, a2]),TyName "int", newconstr @ c1 @ c2)
       end
     | constrain_e (BinOp (e1, Cons, e2)) =
       let
          val (a1,t1,c1) = constrain_e e1
          val (a2,t2,c2) = constrain_e e2
          val newconstr = [(t2,TyCon (t1, TyName "list"))]
       in
          (T.Node ((T.BinOp Cons,TyCon (t1, TyName "list")), [a1,a2]),
               TyCon (t1, TyName "list"), newconstr @ c1 @ c2)
       end
     | constrain_e (BinOp (e1, Eq, e2)) =
       let
          val (a1,t1,c1) = constrain_e e1
          val (a2,t2,c2) = constrain_e e2
       in
          (T.Node ((T.BinOp Eq, TyName "bool"), [a1,a2]), TyName "bool", c1 @ c2)
       end
     | constrain_e (If(cond,e1,e2)) = 
       let
          val (a1,t0,c0) = constrain_e cond
          val (a2,t1,c1) = constrain_e e1
          val (a3,t2,c2) = constrain_e e2
          val tx = TyVar (mkFresh ())
          val newconstr = [(t0,TyName "bool"), (t1,tx), (t2,tx)]
       in
          (T.Node ((T.If,tx), [a1,a2,a3]),tx, newconstr @ c0 @ c1 @ c2)
       end
     | constrain_e (True) = (T.Leaf (T.Boolean, TyName "bool"),TyName "bool",[])
     | constrain_e (False) = (T.Leaf (T.Boolean, TyName "bool"),TyName "bool",[])
     | constrain_e (Let(x,e1,e2)) =
       let
         val _ = pushEnv () 
         val r = if true then 
           let
              val _ = Debug.print_dbg "LET1\n"
              val (a1,t1,c1) = constrain_e e1
              val _ = insertVal (LVar x) t1
              val (a2,t2,c2) = constrain_e e2
           in
              (T.Node ((T.Let x,t2), [a1,a2]),t2,c1 @ c2)
           end
        else
            constrain_e e2  (* FIXME: Something else is meant to happen *)
        val _ = popEnv ()
       in r end
     | constrain_e (List []) = (T.Leaf (T.Nil,TyNil), TyNil,[])
     | constrain_e (List (h::t)) =
       let
          val (a1,t1,c1) = constrain_e h
       in
          (T.Node ((T.List,TyCon(t1,TyName "list")), [a1]), TyCon(t1,TyName "list"), c1)
       end
     | constrain_e (Seq (a,b)) = 
       let
          val (a1,t1,c1) = constrain_e a
          val (a2,t2,c2) = constrain_e b
       in
          (T.Node((T.Seq,t2),[a1,a2]),t2,c2 @ c1)
       end
     | constrain_e x = raise (Fail ("Unhandled case: " ^ ppexpr x ^ "\n"))     
   and constrain constr (ValBinding ((s,t),e)) = 
       let
          val t0 = TyVar (mkFresh ())
          val _ = insertVal (LVar s) t0
          val _ = pushEnv ()
          val _ = pushRemapping ()
          val (a1,t1,c1) = constrain_e e
        
          val _ = Debug.print_dbg ("VENV: " ^ ppenv (#va (!env)) ^ "\n") 

          val _ = popEnv ()
          val _ = popRemapping ()
          val newconstr = [(t0,t1)]
          val _ = Debug.print_dbg ("CONSTR: " ^ ppenv (c1 @ newconstr @ constr) ^ "\n") 
       in
          (T.Node((T.ValBinding s,t0), [a1]), c1 @ newconstr @ constr)
       end
     | constrain c x = (T.Leaf (T.Unit,TyNil), c)

   
   and substinty (TyVar x1) tyT tyS =
     let
        (*val _ = Debug.print_dbg ("TyX: " ^ Int.toString x1 ^ " tyS: " ^ ppty tyS ^ " tyT: " ^ ppty tyT ^ "\n")*)
        fun f tyS = 
         (case tyS of (TyArrow(tyS1,tyS2)) => (TyArrow(f tyS1,f tyS2))
                    | (TyVar n) => if n = x1 then tyT else (TyVar n)
                    | (TyName s) => TyName s
                    | (LVar s) => LVar s
                    | (TyPoly s) => TyPoly s
                    | (TyCon (tyS1,tyS2)) => (TyCon (f tyS1, f tyS2))
                    | TyNil => TyNil)
     in
        f tyS
     end
     | substinty (TyPoly x1) tyT tyS =
     let
         fun f tyS = 
         (case tyS of (TyArrow(tyS1,tyS2)) => (TyArrow(f tyS1,f tyS2))
                    | (TyVar n) => (TyVar n)
                    | (TyName s) => TyName s
                    | (LVar s) => LVar s
                    | (TyPoly s) => if s=x1 then tyT else TyPoly s
                    | (TyCon (tyS1,tyS2)) => (TyCon (f tyS1, f tyS2))
                    | TyNil => TyNil)
     in
        f tyS
     end
     | substinty t1 t2 t3 = 
       raise Fail ("Unhandled subst: " ^ ppty t1 ^ ", " ^ ppty t2 ^ ", " ^ ppty t3)

   and applysubst constr tyT =
       List.foldl (fn ((TyVar(tyX),tyC2),tyS) => 
           substinty (TyVar tyX) tyC2 tyS) tyT (List.rev constr)

   and substinconstr tyX tyT constr =
       (globalTypedAst := map (TypedAST.substinTypedAst tyX tyT) (!globalTypedAst);List.map (fn (tyS1,tyS2) => 
         (substinty tyX tyT tyS1,
          substinty tyX tyT tyS2)) constr)

   and substinconstr_rhs tyX tyT constr =
       List.map (fn (tyS1,tyS2) =>
         (tyS1,
          substinty tyX tyT tyS2)) constr

   and occursin (TyVar tyX) tyT =
     let
        fun oc tyT = (case tyT of
            TyArrow(tyT1,tyT2) => oc tyT1 orelse oc tyT2
          | TyCon(tyT1,tyT2) => oc tyT1 orelse oc tyT2
          | TyName s => false
          | TyVar x => (x = tyX)
          | TyPoly s => false)
     in
        oc tyT
     end

   and generalize constr =
     let
        fun collect (TyVar x) = [TyVar x]
          | collect (TyArrow (x,y)) = collect x @ collect y
          | collect (LVar x) = [LVar x]
          | collect (TyName s) = [TyName s]
          | collect (TyPoly s) = [TyPoly s]
          | collect (TyCon (x,y)) = collect x
          | collect (TyNil) = [TyNil] 

        fun collect_all l [] = l
          | collect_all l ((k,v)::t) = collect_all (collect v @ l) t

        fun mkuniq [] = []
          | mkuniq (h::t) = h :: (List.filter (fn x => x <> h) (mkuniq t))
         
        val envterms = mkuniq (collect_all [] (#va (!env)))

        val domterms = mkuniq (map (fn (x,y) => x) constr)

        fun contains l x = List.exists (fn y => x = y) l

        fun disj [] t = [] 
          | disj t [] = []
          | disj (h::t) l = if contains l h then disj t l else h :: disj t l
        
        val disterms = disj envterms domterms

        val _ = app (fn x => Debug.print_dbg ("DISJ: " ^ ppty x ^ "\n")) disterms

        val polynames = ref 0
        fun mkPoly x = 
          let
             val v = Char.chr (!polynames + (Char.ord #"a"))
             val _ = polynames := !polynames + 1
          in
             (x,TyPoly ("'" ^ Char.toString v))
          end

        val constr' = unify ((map mkPoly disterms) @ constr)
     in
	constr'
     end
   and unify [] = []
     | unify ((tyS,TyVar x) :: rest) = 
        if tyS = (TyVar x) then unify rest
        else if occursin (TyVar x) tyS then
           (raise (Fail "Circular constraints"))
        else 
           (unify (substinconstr (TyVar x) tyS rest)) @ [(TyVar x,tyS)]
     | unify ((TyVar x,tyT)::rest) =
        if tyT = (TyVar x) then unify rest
        else if occursin (TyVar x) tyT then
           (raise (Fail "Circular constraints"))
        else (unify (substinconstr (TyVar x) tyT rest)) @ [(TyVar x,tyT)]
     | unify ((TyArrow(tyS1,tyS2),TyArrow(tyT1,tyT2)) :: rest) =
        unify ((tyS1,tyT1) :: (tyS2,tyT2) :: rest)
     | unify ((TyNil, TyCon(_,TyName "list")) :: rest ) = unify rest 
     | unify ((TyCon(_,TyName "list"), TyNil) :: rest ) = unify rest
     | unify ((TyName a, TyPoly b) :: rest) =
            (unify (substinconstr (TyPoly b) (TyName a) rest)) @ [(TyPoly b,TyName a)]
     | unify ((TyCon (a, b), TyCon (c, d)) :: rest) = (Debug.print_dbg ("TYCON UNIFY: " ^ ppty a ^ " with " ^ ppty c ^ " and " ^ ppty b ^ " with " ^ ppty d ^ "\n");unify ((a,c)::(b,d)::rest))
     | unify ((TyPoly a, TyName b) :: rest) = 
            (unify (substinconstr (TyPoly a) (TyName b) rest)) @ [(TyPoly a,TyName b)]
     | unify ((TyPoly a, TyPoly b) :: rest) = if a = b then unify rest else raise (Fail ("Unsolvable polymorphic unification! " ^ a ^ " <> " ^ b ^ "\n"))
     | unify ((TyName a, TyName b) :: rest) =
        if a = b then unify rest else (raise (Fail ("Unsolvable: " ^ a ^ " <> " ^ b)))
     | unify ((tyS,tyT)::rest) = raise (Fail ("Unsolvable: " ^ ppty tyS ^ " <> " ^ ppty tyT))

   fun replaceInEnv [] = ()
     | replaceInEnv ((k,v)::t) = 
       (env := {ty=(#ty (!env)), va=(substinconstr k v (#va (!env))), be=(#be (!env))};replaceInEnv t)

   fun fixPolyNames () =
     let
        val polyN = ref 0
       
        fun mkPoly () = 
          let
             val v = !polyN
             val _ = polyN := v + 1
          in
             TyPoly ("'" ^ Char.toString (Char.chr (v + (Char.ord #"a"))))
          end

 
        fun fixOne sn (TyArrow(t1,t2)) = 
          let
             val (sn',t1') = fixOne sn t1
             val (sn'', t2') = fixOne sn' t2
          in
             (sn'', TyArrow (t1',t2'))
          end
          | fixOne sn (TyCon(t1,t2)) = 
          let
             val (sn',t1') = fixOne sn t1
             val (sn'', t2') = fixOne sn' t2
          in
             (sn'', TyCon (t1',t2'))
          end
          | fixOne sn (TyVar s) = 
            if contains_h (TyVar s) sn then 
                (sn, lookup_h (TyVar s) sn)
            else
                let
                   val nn = mkPoly()
                   val sn' = (TyVar s, nn) :: sn
                in
                   (sn', nn)
                end
          | fixOne sn x = (sn, x)

         fun envFold [] = []
           | envFold ((k,v)::t) = 
           let
              val (_,v') = if not (containsTy k) then fixOne [] v else ([],v)
              val _ = polyN := 0
           in
              (k,v') :: envFold t
           end
      in
           (env := {ty = (#ty (!env)), va = (envFold (#va (!env))), be = (#be (!env))}) 
      end
                
                

      fun stype x = 
       let
          fun constrF (c,cx) = 
            let
               val (a1,cx') = constrain cx c
               val _ = (globalTypedAst := ((!globalTypedAst) @ [a1]))
               val cr' = unify cx'
               val _ = replaceInEnv cr'
               val _ = fixPolyNames ()
            in
               cr'
            end
               
          val constr = List.foldl constrF [] x 
          val cr = unify (constr)
          val _ = replaceInEnv cr
       (*   val _ = fixPolyNames () *)
       in
          (!globalTypedAst,constr)
       end

   fun pstype x = 
     let
        val (ast,constr) = stype x
        val _ = Debug.print_dbg ("Constraints:\n" ^ (ppenv constr) ^ "\n")
        val _ = Debug.print_dbg ("ValEnv:\n" ^ (ppenv (#va (!env))) ^ "\n")
        val _ = Debug.print_dbg ("TypedAST:\n" ^ (TypedAST.pptypedast ast) ^ "\n")
     in
        ()
     end


end


