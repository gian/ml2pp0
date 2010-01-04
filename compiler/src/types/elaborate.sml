structure Elaborate =
struct
	open Ast
	open AstOps
	
	datatype constraint_lhs = Symbol of symbol
	                        | TyVar of ty
	
	type constraint_set = (constraint_lhs * ty) list

	val tenv = ref [] : constraint_set ref
	val venv = ref [] : constraint_set ref
	val tv = ref 0;

	fun add_vconstr (l,r) = venv := (l,r) :: (!venv)
	fun add_tconstr (l,r) = tenv := (l,r) :: (!tenv)
	
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
			val rt = fresh_ty ()
		in
			()
		end
	
end

