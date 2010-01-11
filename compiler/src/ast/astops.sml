structure AstOps =
struct
	open Ast
	structure T = Types

	type ast_map_funs = {
		decfun : dec -> dec,
		expfun : ast -> ast,
		bindfun : bind -> bind,
		tyfun : ty -> ty,
		oprfun : opr -> opr,
		clausesfun : clause list -> clause list,
		clausefun : clause -> clause
	}

	fun ast_map_decs (f:ast_map_funs) x = 
		map (fn k => (ast_map_dec f k)) x
	and ast_map_dec (f:ast_map_funs) (ExpDec exp) = 
	  	(#decfun f) (ExpDec (ast_map_exp f exp))
	  | ast_map_dec f NullDec = (#decfun f) NullDec
	  | ast_map_dec f (LocalDec) =
	  	(#decfun f) LocalDec 
	  | ast_map_dec f (ValDec {tyvars,valBind,recBind}) =
	    (#decfun f) (ValDec {
							 tyvars=tyvars,
							 valBind=ast_map_binds f valBind,
							 recBind=ast_map_binds f recBind})
	  | ast_map_dec f (FunDec (tyvars,clauses)) =
	  	(#decfun f) (FunDec (tyvars,
							 map (ast_map_clauses f) clauses))
	  | ast_map_dec f (TypeDec tyBind) =
	  	(#decfun f) (TypeDec (ast_map_binds f tyBind))
	  | ast_map_dec f (fd as FixDec (fixity,ops,symtab)) =
	  	(#decfun f) fd
	  | ast_map_dec f x = (#decfun f) x
	and ast_map_exp f (n as Node (nv,t,s,ch)) = (#expfun f) (Node (nv,t,s,map (ast_map_exp f) ch))
	and ast_map_match f x = x
	and ast_map_clauses f c = (#clausesfun f) (map (ast_map_clause f) c)
	and ast_map_clause f {pats,resultType,body} =
		(#clausefun f) {pats=map (ast_map_exp f) pats,
						resultType=resultType,
						body=ast_map_exp f body}
	and ast_map_binds f x = map (ast_map_bind f) x
	and ast_map_bind f (ValBind (p,e)) = (#bindfun f) 
									     (ValBind (ast_map_exp f p,
												  ast_map_exp f e))
	  | ast_map_bind f (ValRecBind (p,m)) = 
	  	(#bindfun f) (ValRecBind (ast_map_exp f p,
								  map (ast_map_exp f) m))
	  | ast_map_bind f x = (#bindfun f) x
	and ast_map_symtab f st =
		let
			val {venv,tenv,iter_order} = !st

			fun maybeUpdT x = x

			fun upd env NONE _ = 
				raise Fail "[BUG] ast_map_symtab updates unknown symbol"
			  | upd env (SOME s) (t,SOME e) = 
			  		Symtab.insert_v st s (t, SOME (ast_map_exp f e))
			  | upd env _ _ = ()

			val vkeys = Symbol.keys (!venv)
			val tkeys = Symbol.keys (!tenv)
		in
			(List.app (fn (s,(t,e)) => 
				upd venv (Symbol.unhash s) (t,e)) vkeys;
			List.app (fn (s,(t,e)) => 
				upd tenv (Symbol.unhash s) (t,e)) tkeys;
			st)
		end
	val ast_map = ast_map_decs

	fun ast_map_top_level f = ast_map_symtab f Symtab.top_level

	fun opr_to_symbol x = Symbol.fromString (PrettyPrint.ppopr x)

	(* FIXME - not all types are compared property *)
	fun ty_eq (TupleTy l) (TupleTy m) = false 
	  | ty_eq (ArrowTy (ty1, ty2)) (ArrowTy (ty1',ty2')) = 
	  		(ty_eq ty1 ty1') andalso (ty_eq ty2 ty2')
	  | ty_eq (VarTy s) (VarTy s') = s = s'
	  | ty_eq (RecordTy x) (RecordTy y) = false 
	  | ty_eq UnitTy UnitTy = false
	  | ty_eq (TyConTy (ty,l)) (TyConTy (ty',l')) = (ty_eq ty ty')
	  | ty_eq (UVar i) (UVar j) = i = j
	  | ty_eq _ _ = false

end
