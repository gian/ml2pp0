structure Elaborate =
struct
	open Ast
	open AstOps

	datatype constraint_lhs = Symbol of symbol
	                        | TyVar of ty

	fun constr_eq (Symbol s) (Symbol s') = s = s'
	  | constr_eq (TyVar ty) (TyVar ty') = ty_eq ty ty'
	  | constr_eq _ _ = false

	type constraint_set = (constraint_lhs * ty) list

	val tenv = ref [] : constraint_set ref
	val venv = ref [] : constraint_set ref
	val tv = ref 0;

	fun add_vconstr (l,r) = venv := (l,r) :: (!venv)
	fun add_tconstr (l,r) = tenv := (l,r) :: (!tenv)

	fun get_vconstr l = 
		List.find (fn (p,q) => constr_eq l p) (!venv)
	
	fun get_tconstr l = 
		List.find (fn (p,q) => constr_eq l p) (!tenv)
	
	fun fresh_ty () = VarTy (Symbol.fromString 
								("?X." ^ Int.toString (
									tv := !tv + 1; !tv)))

	fun print_constr [] = ()
	  | print_constr ((l,r)::t) = 
	  	let
			fun prlhs (Symbol s) = Symbol.toString s
			  | prlhs (TyVar ty) = PrettyPrint.ppty ty
			
			val _ = print (prlhs l ^ " : " ^ PrettyPrint.ppty r ^ "\n")
		in
			print_constr t
		end

	fun constr_e (Var {attr,name}) =
		let
			val rt = (case get_vconstr (Symbol name) of
				NONE => fresh_ty ()
			  | (SOME (_,x)) => x)

			val _ = add_vconstr (Symbol name, rt)
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
					val _ = add_vconstr (TyVar r1, ArrowTy (r, r2))
				in
					r2
				end) init exps'
		end
	  | constr_e (Fn {attr,match}) =
	  	let
			val (p,e) = hd match
			val r1 = constr_p p
			val r2 = constr_e e
			val r0 = fresh_ty ()
			val _ = add_vconstr (TyVar r0, ArrowTy (r1,r2))
			val _ = app (fn (p',e') => 
							let
								val r3 = constr_p p'
								val r4 = constr_e e'
							in
								(add_vconstr (TyVar r3, r1);
								 add_vconstr (TyVar r4, r2))
							end) (tl match)
		in
			r0
		end
	  | constr_e (Int _) = Types.tyInt
	  | constr_e _ = fresh_ty ()

	and constr_p (ConstraintPat (p,t)) =
		let
			val r = constr_p p
			val _ = add_vconstr (TyVar r, t)
		in
			r
		end
	  | constr_p (VarPat {name,...}) =
	  	let
			val r = fresh_ty ()
			val _ = add_vconstr (Symbol name, r)
		in
			r
		end
	  | constr_p (ConstPat e) = constr_e e
	  | constr_p x = raise (Fail ("Unhandled pattern: " ^ PrettyPrint.pppat x))
	and constr' (ValDec v) =
		(case (hd (#valBind v)) of
			(ValBind (Wild,e)) => constr_e e
		  | (ValBind (_,e)) => constr_e e
		  | _ => raise Fail "unknown valdec bind\n")
	  | constr' _ = fresh_ty ()

	fun constr l = 
		let
			val _ = map constr' l
		in
			()
		end

end

