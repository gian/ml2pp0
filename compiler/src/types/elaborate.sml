structure Elaborate =
struct
	open Ast
	open AstOps

	val constr_eq = ty_eq

	type constraint_set = (ty * ty) list

	val tenv = ref [] : constraint_set ref
	val venv = ref [] : constraint_set ref
	val tv = ref 0;
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

	fun print_constr [] = ()
	  | print_constr ((l,r)::t) = 
	  	let
			fun prlhs ty = PrettyPrint.ppty ty
			
			val _ = print (prlhs l ^ " : " ^ PrettyPrint.ppty r ^ "\n")
		in
			print_constr t
		end

	(* TODO These should probably go away *)
	fun opr_constr BOr = (Types.tyBool,Types.tyBool,Types.tyBool)
	  | opr_constr BAnd = (Types.tyBool,Types.tyBool,Types.tyBool)
	  | opr_constr Plus = (Types.tyInt,Types.tyInt,Types.tyInt)
	  | opr_constr Minus = (Types.tyInt,Types.tyInt,Types.tyInt)
	  | opr_constr Times = (Types.tyInt,Types.tyInt,Types.tyInt)
	  | opr_constr Div = (Types.tyInt,Types.tyInt,Types.tyInt)
	  | opr_constr RDiv = (Types.tyReal,Types.tyReal,Types.tyReal)
	  | opr_constr StrConcat = 
	  	(Types.tyString,Types.tyString,Types.tyString)
	  | opr_constr Cons = 
	  	let
			val r0 = fresh_ty ()
			val r1 = ListTy r0
		in
			(r0,r1,r1)
		end
	  | opr_constr Concat =
		let
			val r0 = fresh_ty ()
			val r1 = ListTy r0 
		in
			(r1,r1,r1)
		end
	  | opr_constr Mod = (Types.tyInt, Types.tyInt, Types.tyInt) 
	  | opr_constr Equal = (fresh_ty (), fresh_ty (), Types.tyBool) 
	  | opr_constr NEqual = (fresh_ty (), fresh_ty (), Types.tyBool) 
	  | opr_constr GT = (Types.tyInt, Types.tyInt, Types.tyBool) 
	  | opr_constr LT = (Types.tyInt, Types.tyInt, Types.tyBool) 
	  | opr_constr LTEqual = (Types.tyInt, Types.tyInt, Types.tyBool) 
	  | opr_constr GTEqual = (Types.tyInt, Types.tyInt, Types.tyBool) 
	  | opr_constr _ = (fresh_ty (), fresh_ty (), fresh_ty ())

	fun constr_binop (lc,rc,gc) l r ret =
		(add_vconstr (l, lc);
		 add_vconstr (r, rc);
		 add_vconstr (ret, gc))

	fun constr_e (Var {attr,name,symtab}) =
		let
			val rt = (case Symtab.lookup_v symtab name of
				(NONE,x) => 
				let
					val r' = fresh_ty ()
					val _ = Symtab.insert_v symtab name (SOME r',x)
			val _ = print ("Var " ^ Symbol.toString name ^ " got type " ^ PrettyPrint.ppty r' ^ "\n")
				in
					r'
				end
			  | (SOME t,_) => t) handle _ => (print "Var raised exn\n";
			  									fresh_ty())


			val _ = print ("Var " ^ Symbol.toString name ^ " has type " ^ PrettyPrint.ppty rt ^ "\n")

		in
			rt
		end
	  | constr_e (App {attr,exps=[tm1,tm2]}) =
	  	let
			fun inst tyS (PolyTy x) = 
				(venv := substinconstr (PolyTy x) tyS (!venv); tyS)
			  | inst tyS (ArrowTy (t1,t2)) = 
			  	ArrowTy (inst tyS t1, inst tyS t2)
			  | inst tyS (ListTy s) =
			  	ListTy (inst tyS s)
			  | inst tyS x = x

			val t1' = constr_e tm1
			val t1 = inst (fresh_ty()) t1'
			val t2 = constr_e tm2
			val tx = fresh_ty ()

			val _ = add_vconstr (t1,ArrowTy(t2,tx))
		in
			t1
		end
	  | constr_e (App {attr,exps}) =
	  	let
			val exps' = List.rev (tl (List.rev exps))
			val frst = hd (List.rev exps)
			val init = constr_e frst

			fun inst tyS (PolyTy x) = 
				(venv := substinconstr (PolyTy x) tyS (!venv); tyS)
			  | inst tyS (ArrowTy (t1,t2)) = 
			  	ArrowTy (inst tyS t1, inst tyS t2)
			  | inst tyS (ListTy s) =
			  	ListTy (inst tyS s)
			  | inst tyS x = x
		in
	  		List.foldr (fn (exp,r) =>
				let
					val r0 = constr_e exp
					val r1 = inst (fresh_ty()) r0
					val r2 = fresh_ty ()
					val _ = add_vconstr (r0, ArrowTy (r1, r2))
				in
					r2
				end) init exps'
		end
	  | constr_e (Fn {attr,match,symtab,ty=SOME ty}) =
	  	let
			val _ = print ("**** Fn\n")

			val _ = Symtab.print_scope symtab

			val (p,e) = hd match
			val r0 = fresh_ty ()
			val r1 = constr_p p
			val r2 = constr_e e
			val _ = constr symtab
			val _ = add_vconstr (r0,ArrowTy (r1,r2))
			val _ = substinprog ty r0 
			val _ = app (fn (p',e') => 
							let
								val r3 = constr_p p'
								val r4 = constr_e e'
							in
								(add_vconstr (r3, r1);
								 add_vconstr (r4, r2))
							end) (tl match)
		in
			r0
		end
	  | constr_e (Fn {attr,match,symtab,ty=NONE}) =
	  	raise Fail "Fn without unique type"
	  | constr_e (If {attr,cond,tbr,fbr}) =
	  	let
			val _ = print ("****: If\n")
			val r0 = fresh_ty ()
			val ct = constr_e cond
			val tt = constr_e tbr
			val ft = constr_e fbr
			val _ = add_vconstr (r0,tt)
			val _ = add_vconstr (r0,ft)
			val _ = add_vconstr (tt,ft)
			val _ = add_vconstr (ct,Types.tyBool)
		in
			r0
		end
	  | constr_e (Int _) = Types.tyInt
	  | constr_e (String _) = Types.tyString
	  | constr_e (Bool _) = Types.tyBool
	  | constr_e (Real _) = Types.tyReal
	  | constr_e (Word _) = Types.tyWord
	  | constr_e (Char _) = Types.tyChar
	  | constr_e (List {attr,exps=[]}) = ListTy (fresh_ty ())
	  | constr_e (List {attr,exps}) =
	  	let
			val le = constr_e (hd exps)
			(* FIXME should add constraints for all list items *)
			val lt = fresh_ty ()
			val _ = add_vconstr (le,lt)
		in
			ListTy lt
		end
	  | constr_e (BuiltIn (s,ty)) = ty
	  | constr_e (Let {attr,decs,exp,symtab}) = 
	  	let
	  		val _ = constr symtab
	   	in
			constr_e exp
		end
	  | constr_e (BinOp {attr,opr,lhs,rhs}) = 
	  	let
			val rl = constr_e lhs
			val rr = constr_e rhs
			val ret = fresh_ty ()
			val cs = opr_constr opr
			val _ = constr_binop cs rl rr ret
		in
			ret
		end
	  | constr_e e = raise Fail ("Unhandled: " ^ PrettyPrint.ppexp e)

	and constr_p (ConstraintPat (p,t)) =
		let
			val r = constr_p p
			val _ = add_vconstr (r, t)
		in
			r
		end
	  | constr_p (VarPat {name,symtab,...}) =
	  	let
			val r = fresh_ty ()
			
			val (_,e) = Symtab.lookup_v symtab name
			val _ = Symtab.insert_v symtab name (SOME r, e)
		in
			r
		end
	  | constr_p (TuplePat l) =
	  		TupleTy (map constr_p l)
	  | constr_p (ConstPat e) = constr_e e
	  | constr_p x = raise (Fail ("Unhandled pattern: " ^ PrettyPrint.pppat x))
	and constr' (ValDec v) =
		(case (hd (#valBind v)) of
			(ValBind (Wild,e)) => constr_e e
		  | _ => raise Fail "unknown valdec bind\n")
	  | constr' _ = fresh_ty ()

	and constr symtab = 
		let
			val {venv=ve,tenv,iter_order} = !symtab

			fun upd env s (t,e) = 
			  		Symtab.insert_v symtab s (t,e)

			val vkeys = List.map (fn x => (x, Symtab.lookup_v symtab x))
							(!iter_order)
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
			fun ef (f as Fn {symtab,attr,match,ty=SOME ty}) = 
				(substinenv tyX tyT symtab; 
				 Fn {symtab=symtab,
				 	 attr=attr,
				     match=match,
					 ty=SOME (substinty tyX tyT ty)})
			  | ef (f as Fn {ty=NONE,...}) = f
			  | ef (f as Let {symtab,...}) =
			  	(substinenv tyX tyT symtab; f)
			  | ef f = f

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
				patfun = id,
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
     | unify ((VarTy (a,_), VarTy (b,_)) :: rest) =
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

