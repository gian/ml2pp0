structure Elaborate =
struct
	open Ast
	open AstOps

	val constr_eq = ty_eq

	type constraint_set = (ty * ty) list

	val tenv = ref [] : constraint_set ref
	val venv = ref [] : constraint_set ref
	val tv = ref 50;
	val pv = ref ~1;

	fun add_vconstr (l,r) = (venv := (l,r) :: (!venv);
		print ("add_vconstr: " ^ PrettyPrint.ppty l ^ " = " ^
				PrettyPrint.ppty r ^ "\n"))

	fun add_tconstr (l,r) = tenv := (l,r) :: (!tenv)

	fun get_vconstr l = 
		List.find (fn (p,q) => constr_eq l p) (!venv)
	
	fun get_tconstr l = 
		List.find (fn (p,q) => constr_eq l p) (!tenv)

	fun fresh_ty () = UVar (tv := !tv + 1; !tv)
	fun fresh_poly () = PolyTy (pv := !pv + 1; !pv)

	fun get_match_lhs (Node (Match, _, _, [p,e])) = p
	  | get_match_lhs _ = raise Fail "get_match_lhs called on non-match"

	fun get_match_rhs (Node (Match, _, _, [p,e])) = e
	  | get_match_rhs _ = raise Fail "get_match_rhs called on non-match"

	fun print_constr [] = ()
	  | print_constr ((l,r)::t) = 
	  	let
			fun prlhs ty = PrettyPrint.ppty ty
			
			val _ = print (prlhs l ^ " : " ^ PrettyPrint.ppty r ^ "\n")
		in
			print_constr t
		end

	and inst tyS (PolyTy x) = 
		(venv := substinconstr (PolyTy x) tyS (!venv); tyS)
	  | inst tyS (ArrowTy (t1,t2)) = ArrowTy (inst tyS t1, inst tyS t2)
	  | inst tyS (ListTy s) = ListTy (inst tyS s)
	  | inst tyS (VectorTy (t,x)) = VectorTy (inst tyS t, x)
	  | inst tyS x = x

	and constr_e (Node (Int _, _, _, _)) = IntTy 
	  | constr_e (Node (String _, _, _, _)) = StringTy
	  | constr_e (Node (Word _, _, _, _)) = WordTy
	  | constr_e (Node (Real _, _, _, _)) = RealTy
	  | constr_e (Node (Bool _, _, _, _)) = BoolTy
	  | constr_e (Node (Char _, _, _, _)) = CharTy
	  | constr_e (Node (BuiltIn (_,t), _, _, _)) = t
	  | constr_e (Node (Constraint t, _, _, [e])) =
	  	let
			val t' = constr_e e
			val _ = add_vconstr (t', t)
		in
			t'
		end
	  | constr_e (Node (Case, _, _, body)) =
	  	let
			val cond = hd body
			val t = constr_e cond
			val c1 = hd (tl body)
			val c1l = constr_e (get_match_lhs c1)
			val c1r = constr_e (get_match_rhs c1)
			val _ = add_vconstr (c1l, t)

			(* FIXME: match all clauses *)
		in
			c1r
		end
	  | constr_e (Node (If, _, _, [c,tbr,fbr])) =
	  	let
			val c' = constr_e c
			val _ = add_vconstr (c', BoolTy)
			val tbr' = constr_e tbr
			val fbr' = constr_e fbr
			val rx = fresh_ty ()
			val _ = add_vconstr (tbr', rx)
			val _ = add_vconstr (fbr', rx)
		in
			rx
		end
	  | constr_e (Node (Unit, _, _, _)) = UnitTy 
	  | constr_e (Node (Seq, _, _, es)) =
	  		List.foldl (fn (a,b) => constr_e a) (fresh_ty ()) es
	  | constr_e (Node (Tuple, _, _, es)) =
	  		TupleTy (map constr_e es)
	  | constr_e (Node (List, _, _, es)) =
	  		ListTy (
				List.foldl (fn (a,b) =>
				let
					val rx = fresh_ty ()
					val a' = constr_e a
					val _ = add_vconstr (b, rx)
					val _ = add_vconstr (rx, a')
				in
					rx
				end) (fresh_ty ()) es
			)
	  | constr_e (Node (Vector, _, st, es)) =
	  		VectorTy (
				List.foldl (fn (a,b) =>
				let
					val rx = fresh_ty ()
					val a' = constr_e a
					val _ = add_vconstr (b, rx)
					val _ = add_vconstr (rx, a')
				in
					rx
				end) (fresh_ty ()) es,
				Node (Int (length es),SOME IntTy,st,[])
			)
	  | constr_e (Node (Var s, _, st, _)) =
	  	let
			val t' = (case Symtab.lookup_v st s of
						(SOME ty,_) => ty
					  | (NONE,x) => 
					  	let
							val r = fresh_ty ()
							val _ = Symtab.insert_v st s (SOME r, x)
						in
							r
						end)
		in
			t'
		end

	  | constr_e (Node (App, _, _, [tm1,tm2])) =
		let
			val t1' = constr_e tm1
			val t1 = inst (fresh_ty()) t1'
			val t2 = constr_e tm2
			val tx = fresh_ty ()
 
			val _ = add_vconstr (t1,ArrowTy(t2,tx))
		in
			tx
		end
	  | constr_e (Node (App, _, _, l)) =
	  	let
			val (frst::f) = List.rev l
			val exps' = List.rev f
			val init = constr_e frst
		in
	  		List.foldl (fn (exp,r) =>
				let
					val r0 = constr_e exp
					val r1 = inst (fresh_ty()) r0
					val r2 = fresh_ty ()
					val _ = add_vconstr (r0, ArrowTy (r1, r2))
				in
					r2
				end) init exps'
		end
	  | constr_e (Node (Fn, _, _, matches)) =
	  	let
			val (t1,t2) = constr_m (hd matches)
			val rx = fresh_ty ()
		in
			ArrowTy (rx,t2)
		end
	  | constr_e (Node (WildPat, _, _, _)) = fresh_ty ()
	  | constr_e (Node (VarPat s, _, st, _)) =
	  	let
			val r = (case Symtab.lookup_v st s of
						(SOME t,_) => t
					  | (NONE,x) => 
					  	let
					  		val t = fresh_ty()
							val _ = Symtab.insert_v st s (SOME t, x)
						in
							t
						end)

		in
			r
		end
	  | constr_e n = raise Fail ("constr_e unhandled: " ^ PrettyPrint.ppexp n)

	and constr_m (Node (Match, _, _, [p,e])) =
		(constr_e p, constr_e e)
	  | constr_m _ = raise Fail "constr_m applied to non-match"

	and constr symtab = 
		let
			val {venv=ve,tenv,iter_order} = !symtab

			fun upd env s (t,e) = 
			  		Symtab.insert_v symtab s (t,e)

			val vkeys = List.map (fn x => (x, Symtab.lookup_v symtab x))
							(!iter_order)

			val _ = Symtab.print_scope symtab
		in
			List.app (fn (s,(t,SOME e)) =>
				if s = (Symbol.fromString "__parent_scope") 
				then () else
				let
					val r = fresh_ty ()
					val _ = upd ve s (SOME r, SOME e)
					val _ = print ("INSIDE LIST APP: " ^ PrettyPrint.ppexp e ^ "\n")
					val t' = constr_e e

					val _ = print ("INSIDE LIST APP TY: " ^ PrettyPrint.ppty t' ^ "\n")

					val _ = Symtab.print_scope symtab
				in
					(add_vconstr (r, t');
					 print "\nConstraint Set:\n";
					 print_constr (!venv);
					 venv := unify (!venv);
					print "\nConstraint Set (Unify):\n";
					 print_constr (!venv);
					 venv := generalise (!venv);
					 print "\nConstraint Set (Generalise):\n";
					 print_constr (!venv)
					 )
				end
			  | (s,(t,NONE)) => ()) (List.rev vkeys)
		end


	and substinty (UVar x1) tyT tyS =
		let

        	fun f tyS = 
         	(case tyS of (ArrowTy(tyS1,tyS2)) => (ArrowTy(f tyS1,f tyS2))
				    | (UVar n) => if n = x1 then tyT else (UVar n)
					| (ListTy l) => ListTy (f l)
					| x => x)
     	in
        	f tyS
     	end
	  | substinty (PolyTy x1) tyT tyS =
	  	let
	 		fun f tyS = 
        	(case tyS of (ArrowTy(tyS1,tyS2)) => (ArrowTy(f tyS1,f tyS2))
                    | (ListTy l) => ListTy (f l)
					| (PolyTy n) => if n = x1 then tyT else (PolyTy n)
					| x => x)
		in
        	f tyS
		end
	  | substinty _ _ _ = raise Fail "substinty: invalid argument"

	and substinenv tyX tyT symtab = 
		let
			val {venv,tenv,iter_order} = !symtab

			val vkeys = Symbol.keys (!venv)
		
			fun upd env NONE _ = 
				raise Fail "[BUG] constr updates unknown symbol"
			  | upd env (SOME s) (t,e) = 
			  		Symtab.insert_v symtab s (t,e)
		in
			(List.app (fn (s,(SOME t,e)) =>
				upd venv (Symbol.unhash s) 
					(SOME (substinty tyX tyT t),e)
					| _ => ())
				) vkeys
		end

	and	substinprog (PolyTy tyX) tyT = Symtab.top_level 
	  |	substinprog tyX tyT =
		let
			fun ef (Node(Fn,SOME ty,symtab,ch)) = 
				(substinenv tyX tyT symtab; 
				 Node(Fn,
				 	  SOME (substinty tyX tyT ty),
					  symtab,
					  ch))
			  | ef (f as Node(Let _,t, symtab,ch)) =
			  	(substinenv tyX tyT symtab; f)
			  | ef (Node(c,SOME ty,symtab,ch)) =
			  	Node(c,SOME (substinty tyX tyT ty), symtab, ch)
			  | ef x = x

			fun id x = x

			(*val _ = print "\nTop Level Subst Env Before:\n"
			val _ = Symtab.print_scope Symtab.top_level
			*)
			val _ = substinenv tyX tyT Symtab.top_level
			(*
			val _ = print "\nTop Level Subst Env After:\n"
			val _ = Symtab.print_scope Symtab.top_level*)
		in
			ast_map_symtab {
				decfun = id,
				expfun = ef,
				bindfun = id,
				tyfun = id,
				oprfun = id,
				clausesfun = id,
				clausefun = id} Symtab.top_level
		end


	and substinconstr tyX tyT constr =
		let
			val _ = substinprog tyX tyT

			val _ = print ("   * Type Sub: [" ^
							PrettyPrint.ppty tyX ^ "/" ^
							PrettyPrint.ppty tyT ^ "]\n")
		

			val constr' = map (fn (l,r) => (substinty tyX tyT l, substinty tyX tyT r)) constr
		in
			constr'
		end

	and substinconstr_rhs tyX tyT constr =
		let
			val _ = substinprog tyX tyT
			
			val _ = print ("   * RHS Type Sub: [" ^
							PrettyPrint.ppty tyX ^ "/" ^
							PrettyPrint.ppty tyT ^ "]\n")
		

			val constr' = map (fn (l,r) => (l, substinty tyX tyT r)) constr
		val _ = print_constr constr'
		in
			constr'
		end

	(* FIXME incomplete *)
	and occursin (UVar tyX) tyT =
		let
			fun oc tyT = (case tyT of
				ArrowTy(tyT1,tyT2) => oc tyT1 orelse oc tyT2
			  | UVar x => (x = tyX)
			  | _ => false)
     in
        oc tyT
     end
	  | occursin _ _ = raise Fail "Non-UVar argument to occursin"

	and unify [] = []
      | unify ((tyS,UVar x) :: rest) =  
		if ty_eq tyS (UVar x) then unify rest
        else if occursin (UVar x) tyS then
           (raise (Fail "Circular constraints"))
        else 
           (unify (substinconstr (UVar x) tyS rest)) @ [(UVar x,tyS)]
     | unify ((UVar x,tyT)::rest) =
        if ty_eq tyT (UVar x) then unify rest
        else if occursin (UVar x) tyT then
           (raise (Fail "Circular constraints"))
        else (unify (substinconstr (UVar x) tyT rest)) @ [(UVar x,tyT)]
	 | unify ((IntTy, IntTy) :: rest) = unify rest
	 | unify ((StringTy, StringTy) :: rest) = unify rest
	 | unify ((UnitTy, UnitTy) :: rest) = unify rest
	 | unify ((BoolTy, BoolTy) :: rest) = unify rest
	 | unify ((RealTy, RealTy) :: rest) = unify rest
	 | unify ((CharTy, CharTy) :: rest) = unify rest
	 | unify ((WordTy, WordTy) :: rest) = unify rest
	 | unify ((VectorTy (t1,v1), VectorTy (t2,v2)) :: rest) = 
	 	unify ((t1,t2) :: rest)
     | unify ((ArrowTy(tyS1,tyS2),ArrowTy(tyT1,tyT2)) :: rest) =
        unify ((tyS1,tyT1) :: (tyS2,tyT2) :: rest)
	 | unify ((ListTy tyS1, ListTy tyS2) :: rest) =
	 	unify ((tyS1,tyS2) :: rest)
	 | unify ((PolyTy a, VarTy b) :: rest) = 
            (unify (substinconstr (PolyTy a) (VarTy b) rest)) @ 
				[(PolyTy a,VarTy b)]
     | unify ((PolyTy a, PolyTy b) :: rest) = 
	 		if a = b then unify rest 
			else raise (Fail 
				("Unsolvable polymorphic unification! " ^ 
					PrettyPrint.ppty (PolyTy a) ^ " <> " ^ 
					PrettyPrint.ppty (PolyTy b) ^ "\n"))
     | unify ((VarTy a, VarTy b) :: rest) =
        if a = b then unify rest else (raise (Fail ("Unsolvable: " ^ Symbol.toString a ^ " <> " ^ Symbol.toString b)))
     | unify ((tyS,tyT)::rest) = (Symtab.print_scope (Symtab.top_level); raise (Fail ("Unsolvable: " ^ PrettyPrint.ppty tyS ^ " <> " ^ PrettyPrint.ppty tyT)))

	and generalise env =
		let
			fun collect_tyvars (UVar s) = [UVar s]
			  | collect_tyvars (ArrowTy (t1,t2)) =
			  		collect_tyvars t1 @ collect_tyvars t2
			  | collect_tyvars (ListTy x) = collect_tyvars x
			  | collect_tyvars x = []

			fun unique [] = []
			  | unique ((UVar h)::t) = 
			  		(UVar h) :: (unique 
							(List.filter (fn (UVar x) => 
								x <> h) t))

			val bound = List.foldl (fn ((l,r),a) =>
						unique (collect_tyvars l) @ a) [] env


			val _ = print ("BOUND: " ^ (String.concatWith ", " (map PrettyPrint.ppty bound)) ^ "\n")
			val vars : ty list = unique (List.foldl (fn ((l,r),a) => 
						 (collect_tyvars r) @ a) [] env)

			val _ = print ("VARS: " ^ (String.concatWith ", " (map PrettyPrint.ppty vars)) ^ "\n")
			val free = unique  (List.filter (fn (UVar x) => 
								  not (List.exists 
									(fn (UVar y) => x = y) bound)) vars)

			val _ = print ("FREE: " ^ (String.concatWith ", " (map PrettyPrint.ppty free)) ^ "\n")
			val env' = List.foldl (fn (a,e) => 
						substinconstr_rhs a (fresh_poly ()) e) env free

			val _ = pv := ~1
		in
			env'
		end

	fun unify_constraints () = unify (List.rev (!venv))

end

