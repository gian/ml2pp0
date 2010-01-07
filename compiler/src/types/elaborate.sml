structure Elaborate =
struct
	open Ast
	open AstOps

	val constr_eq = ty_eq

	type constraint_set = (ty * ty) list

	val tenv = ref [] : constraint_set ref
	val venv = ref [] : constraint_set ref
	val tv = ref 0;

	fun add_vconstr (l,r) = venv := (l,r) :: (!venv)
	fun add_tconstr (l,r) = tenv := (l,r) :: (!tenv)

	fun get_vconstr l = 
		List.find (fn (p,q) => constr_eq l p) (!venv)
	
	fun get_tconstr l = 
		List.find (fn (p,q) => constr_eq l p) (!tenv)

	(* FIXME should use the local enclosing scope, not top_level
		- no, we shouldn't.  All tyvars can be top-level, silly.
	*)
	fun fresh_ty () = UVar (tv := !tv + 1; !tv)

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
			val r1 = TyConTy (r0, 
								[VarTy (Symbol.fromString
									"list", Symtab.top_level)])
		in
			(r0,r1,r1)
		end
	  | opr_constr Concat =
		let
			val r0 = fresh_ty ()
			val r1 = TyConTy (r0, 
								[VarTy (Symbol.fromString
									"list", Symtab.top_level)])
		in
			(r1,r1,r1)
		end
	  | opr_constr _ = (fresh_ty (), fresh_ty (), fresh_ty ())

	fun constr_binop (lc,rc,gc) l r ret =
		(add_vconstr (l, lc);
		 add_vconstr (r, rc);
		 add_vconstr (ret, gc))

	fun constr_e (Var {attr,name,symtab}) =
		let
			val rt = (case Symtab.lookup_v symtab name of
				(NONE,_) => raise 
					Fail ("Unknown Var: " ^ Symbol.toString name)
			  | (SOME t,_) => t)
		in
			rt
		end
	  | constr_e (App {attr,exps}) =
	  	let
			val exps' = List.rev (tl (List.rev exps))
			val frst = hd (List.rev exps)
			val init = constr_e frst
		in
	  		List.foldr (fn (exp,r) =>
				let
					val r1 = constr_e exp
					val r2 = fresh_ty ()
					val _ = add_vconstr (r1, ArrowTy (r, r2))
				in
					r2
				end) init exps'
		end
	  | constr_e (Fn {attr,match,symtab}) =
	  	let
			val (p,e) = hd match
			val r1 = constr_p p
			val r2 = constr_e e
			val r0 = fresh_ty ()
			val _ = constr symtab
			val _ = add_vconstr (r0, ArrowTy (r1,r2))
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
	  | constr_e (Int _) = Types.tyInt
	  | constr_e (String _) = Types.tyString
	  | constr_e (Bool _) = Types.tyBool
	  | constr_e (Real _) = Types.tyReal
	  | constr_e (Word _) = Types.tyWord
	  | constr_e (Char _) = Types.tyChar
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
	  | constr_e _ = fresh_ty ()

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
		  | (ValBind (_,e)) => constr_e e
		  | _ => raise Fail "unknown valdec bind\n")
	  | constr' _ = fresh_ty ()

	and constr symtab = 
		let
			val {venv,tenv} = !symtab

			fun upd env NONE _ = 
				raise Fail "[BUG] constr updates unknown symbol"
			  | upd env (SOME s) (t,e) = 
			  		Symtab.insert_v symtab s (t,e)
			  | upd env _ _ = ()


			val vkeys = Symbol.keys (!venv)
		in
			List.app (fn (s,(t,SOME e)) =>
				if s = 
					Symbol.hash (Symbol.fromString "__parent_scope") 
				then () else
				let
					val r = fresh_ty ()
					val _ = upd venv (Symbol.unhash s) (SOME r, SOME e)
					val t' = constr_e e
				in
					add_vconstr (r, t')
				end
			  | (s,(t,NONE)) => ()) vkeys
		end

(*
	Symbol of symbol
    | TyVar of ty

	fun unify [] = []
	  | unify ((TyVar tyS,TyVar (VarTy x)) :: rest) = 
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
*)

end

