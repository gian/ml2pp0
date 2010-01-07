structure AstOps =
struct
	open Ast
	structure T = Types

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

	fun ast_map_decs (f:ast_map_funs) x = 
		map (fn k => (ast_map_dec f k)) x
	and ast_map_dec (f:ast_map_funs) (e as ExpDec {attr,exp}) = 
	  	(#decfun f) (ExpDec {attr=attr,exp=ast_map_exp f exp})
	  | ast_map_dec f (e as NullDec) = (#decfun f) NullDec
	  | ast_map_dec f (LocalDec {attr,dec1,dec2,symtab}) =
	  	(#decfun f) (LocalDec {attr=attr,
							   dec1=ast_map_decs f dec1,
							   dec2=ast_map_decs f dec2,
							   symtab=symtab})
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
	  | ast_map_dec f (fd as FixDec {attr,fixity,ops,symtab}) =
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
	  | ast_map_exp f (List {attr,exps}) =
	    (#expfun f) (List {attr=attr, exps=map (ast_map_exp f) exps})
	  | ast_map_exp f (Constraint {attr,exp,ty}) =
	    (#expfun f) (Constraint {attr=attr,exp=ast_map_exp f exp,ty=ty})
	  | ast_map_exp f (Fn {attr=attr,match=match,symtab}) =
	    (#expfun f) (Fn {attr=attr,
						 match=map (fn (x,y) =>
						 	(ast_map_pat f x,
							 ast_map_exp f y)) match,
							 symtab=ast_map_symtab f symtab})
	  | ast_map_exp f (If {attr,cond,tbr,fbr}) =
	  	(#expfun f) (If {attr=attr,
						 cond=ast_map_exp f cond,
						 tbr=ast_map_exp f tbr,
						 fbr=ast_map_exp f fbr})
	  | ast_map_exp f (Let {attr,decs,exp,symtab}) =
	  	(#expfun f) (Let {attr=attr,
						  decs=ast_map_decs f decs,
						  exp=ast_map_exp f exp,
						  symtab=ast_map_symtab f symtab})
	  | ast_map_exp f x = (#expfun f) x
	and ast_map_binds f x = map (ast_map_bind f) x
	and ast_map_bind f (ValBind (p,e)) = (#bindfun f) 
									     (ValBind (ast_map_pat f p,
												  ast_map_exp f e))
	  | ast_map_bind f (ValRecBind (p,m)) = 
	  	(#bindfun f) (ValRecBind (ast_map_pat f p,
								  map (fn (p',e') => 
								  	(ast_map_pat f p',
								     ast_map_exp f e')) m))
	  | ast_map_bind f x = (#bindfun f) x
	and ast_map_match f x = x
	and ast_map_pat f (AsPat (l,r)) = 
		(#patfun f) (AsPat (ast_map_pat f l, ast_map_pat f r))
	  | ast_map_pat f (ConstraintPat (p,t)) =
	  	(#patfun f) (ConstraintPat (ast_map_pat f p, t))
	  | ast_map_pat f (AppPat l) =
	  	(#patfun f) (AppPat (map (ast_map_pat f) l))
	  | ast_map_pat f (TuplePat l) =
	  	(#patfun f) (TuplePat (map (ast_map_pat f) l))
	  | ast_map_pat f (ListPat l) =
	  	(#patfun f) (ListPat (map (ast_map_pat f) l))
	  | ast_map_pat f k = (#patfun f) k
	and ast_map_clauses f c = (#clausesfun f) (map (ast_map_clause f) c)
	and ast_map_clause f {pats,resultType,body} =
		(#clausefun f) {pats=map (ast_map_pat f) pats,
						resultType=resultType,
						body=ast_map_exp f body}
	and ast_map_symtab f st =
		let
			val {venv,tenv} = !st

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

	fun e_attr (Handle {attr,...}) = attr
	  | e_attr (App {attr,...}) = attr
	  | e_attr (BinOp {attr,...}) = attr
	  | e_attr (Constraint {attr,...}) = attr
	  | e_attr (Fn {attr,...}) = attr
	  | e_attr (Case {attr,...}) = attr
	  | e_attr (While {attr,...}) = attr
	  | e_attr (If {attr,...}) = attr
	  | e_attr (Raise {attr,...}) = attr
	  | e_attr (Op {attr,...}) = attr
	  | e_attr (Var {attr,...}) = attr
	  | e_attr (Selector {attr,...}) = attr
	  | e_attr (Record {attr,...}) = attr
	  | e_attr (Seq {attr,...}) = attr
	  | e_attr (Tuple {attr,...}) = attr
	  | e_attr (List {attr,...}) = attr
	  | e_attr (Let {attr,...}) = attr
	  | e_attr _ = []

	fun set_e_attr a (Handle r) = 
		Handle {attr=a :: (#attr r),
				exp= #exp r,
				match= #match r}
	  | set_e_attr a (App r) = 
	  	App {attr=a :: (#attr r),
				exps= #exps r}
	  | set_e_attr a (BinOp r) =
	  	BinOp {attr=a :: (#attr r),
			   opr= #opr r,
			   lhs= #lhs r,
			   rhs= #rhs r}
	  | set_e_attr a (Constraint r) =
	  	Constraint {attr=a :: (#attr r),
					exp= #exp r,
					ty= #ty r}
	  | set_e_attr a (Fn r) =
	  	Fn {attr=a :: (#attr r),
			match= #match r,
			symtab= #symtab r}
	  | set_e_attr a (Case r) = Case r 
	  | set_e_attr a (While r) = While r
	  | set_e_attr a (If r) = If
	  				{attr=a :: (#attr r),
					 cond= #cond r,
					 tbr= #tbr r,
					 fbr = #fbr r}
	  | set_e_attr a (Raise r) = Raise r 
	  | set_e_attr a (Op r) = Op r
	  | set_e_attr a (Var r) = 
	  	Var {attr=a :: (#attr r),
		     name= #name r,
			 symtab = #symtab r}
	  | set_e_attr a (Selector r) = Selector r
	  | set_e_attr a (Record r) = Record r
	  | set_e_attr a (Seq r) = Seq r
	  | set_e_attr a (Tuple r) = Tuple r
	  | set_e_attr a (List r) = List r
	  | set_e_attr a (Let r) = Let r
	  | set_e_attr a x = x

	fun e_attr_ty (Int _) = SOME T.tyInt
	  | e_attr_ty (Word _) = SOME T.tyWord
	  | e_attr_ty (Real _) = SOME T.tyReal
	  | e_attr_ty (String _) = SOME T.tyString
	  | e_attr_ty (Char _) = SOME T.tyChar
	  | e_attr_ty (Bool _) = SOME T.tyBool
	  | e_attr_ty x = 
	  		(fn (SOME (Type t)) => SOME t 
			  | _ => NONE)
			(List.find (fn (Type x) => true | _ => false) (e_attr x))

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
