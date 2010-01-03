structure AstOps =
struct
	open Ast

	type ast_map_funs = {
		decfun : dec -> dec,
		expfun : exp -> exp,
		patfun : pat -> pat,
		bindfun : bind -> bind,
		tyfun : ty -> ty,
		oprfun : opr -> opr,
		clausesfun : clause list -> clause list,
		clausefun : clause -> clause
	}

	fun ast_map_decs (f:ast_map_funs) x = map (fn k => (print "MAP\n"; ast_map_dec f k)) x
	and ast_map_dec (f:ast_map_funs) (e as ExpDec {attr,exp}) = 
	  	(#decfun f) (ExpDec {attr=attr,exp=ast_map_exp f exp})
	  | ast_map_dec f (e as NullDec) = (#decfun f) NullDec
	  | ast_map_dec f (LocalDec {attr,dec1,dec2}) =
	  	(#decfun f) (LocalDec {attr=attr,
							   dec1=ast_map_decs f dec1,
							   dec2=ast_map_decs f dec2})
	  | ast_map_dec f (ValDec {attr,tyvars,valBind,recBind}) =
	    (#decfun f) (ValDec {attr=attr,
							 tyvars=tyvars,
							 valBind=ast_map_binds f valBind,
							 recBind=ast_map_binds f recBind})
	  | ast_map_dec f (FunDec {attr,tyvars,clauses}) =
	  	(#decfun f) (FunDec {attr=attr,
							 tyvars=tyvars,
							 clauses=map (ast_map_clauses f) clauses})
	  | ast_map_dec f (TypeDec {attr,tyBind}) =
	  	(#decfun f) (TypeDec {attr=attr,tyBind=ast_map_binds f tyBind})
	  | ast_map_dec f (fd as FixDec {attr,fixity,ops}) =
	  	(#decfun f) fd
	  | ast_map_dec f x = (#decfun f) x
	and ast_map_exp f (Handle {attr,exp,match}) = 
		(#expfun f) (Handle {attr=attr, 
							 exp=ast_map_exp f exp,
							 match=ast_map_match f match})
	  | ast_map_exp f (App {attr,exps}) =
	    (#expfun f) (App {attr=attr,exps=map (ast_map_exp f) exps})
	  | ast_map_exp f (BinOp {attr,opr,lhs,rhs}) =
	    (#expfun f) (BinOp {attr=attr,opr=opr,lhs=ast_map_exp f lhs,
							rhs=ast_map_exp f rhs})
	  | ast_map_exp f (Constraint {attr,exp,ty}) =
	    (#expfun f) (Constraint {attr=attr,exp=ast_map_exp f exp,ty=ty})
	  | ast_map_exp f (Fn {attr=attr,match=match}) =
	    (#expfun f) (Fn {attr=attr,
						 match=map (fn (x,y) =>
						 	(ast_map_pat f x,
							 ast_map_exp f y)) match})
	  | ast_map_exp f (If {attr,cond,tbr,fbr}) =
	  	(#expfun f) (If {attr=attr,
						 cond=ast_map_exp f cond,
						 tbr=ast_map_exp f tbr,
						 fbr=ast_map_exp f fbr})
	  | ast_map_exp f (Let {attr,decs,exp}) =
	  	(#expfun f) (Let {attr=attr,
						  decs=ast_map_decs f decs,
						  exp=ast_map_exp f exp})
	  | ast_map_exp f x = (#expfun f) x
	and ast_map_binds f x = map (ast_map_bind f) x
	and ast_map_bind f (ValBind (p,e)) = (#bindfun f) 
									     (ValBind (ast_map_pat f p,
												  ast_map_exp f e))
	  | ast_map_bind f x = (#bindfun f) x
	and ast_map_match f x = x
	and ast_map_pat f x = x
	and ast_map_clauses f c = (#clausesfun f) (map (ast_map_clause f) c)
	and ast_map_clause f {pats,resultType,body} =
		(#clausefun f) {pats=map (ast_map_pat f) pats,
						resultType=resultType,
						body=ast_map_exp f body}
	val ast_map = ast_map_decs

end
