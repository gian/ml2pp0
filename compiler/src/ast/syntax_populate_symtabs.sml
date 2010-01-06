structure SyntaxPopulateSymtabs : SYNTAX_PASS =
struct
	type syntax_pass_param = unit

	open Ast
	
	(* Do a pass over the AST and populate symtab fields appropriately *)
	fun symtab_popl_decs scope x = 
		map (fn k => (symtab_popl_dec scope k)) x
	and symtab_popl_dec scope (e as ExpDec {attr,exp}) = 
	  	 (ExpDec {attr=attr,exp=symtab_popl_exp scope exp})
	  | symtab_popl_dec scope (e as NullDec) =  NullDec
	  | symtab_popl_dec scope (LocalDec {attr,dec1,dec2,symtab}) =
	  	 (LocalDec {attr=attr,
							   dec1=symtab_popl_decs symtab dec1,
							   dec2=symtab_popl_decs symtab dec2,
							   symtab=symtab})
	  | symtab_popl_dec scope (ValDec {attr,tyvars,valBind,recBind}) =
	     (ValDec {attr=attr,
							 tyvars=tyvars,
							 valBind=symtab_popl_binds scope valBind,
							 recBind=symtab_popl_binds scope recBind})
	  | symtab_popl_dec scope (FunDec {attr,tyvars,clauses}) =
	  	 (FunDec {attr=attr,
				  tyvars=tyvars,
				  clauses=map (symtab_popl_clauses scope) clauses})
	  | symtab_popl_dec scope (TypeDec {attr,tyBind}) =
	  	 (TypeDec {attr=attr,tyBind=symtab_popl_binds scope tyBind})
	  | symtab_popl_dec scope (fd as FixDec {attr,fixity,ops,symtab}) =
	  	 fd
	  | symtab_popl_dec scope x =  x
	and symtab_popl_exp scope (Handle {attr,exp,match}) = 
		 (Handle {attr=attr, 
							 exp=symtab_popl_exp scope exp,
							 match=symtab_popl_match scope match})
	  | symtab_popl_exp scope (App {attr,exps}) =
	     (App {attr=attr,exps=map (symtab_popl_exp scope) exps})
	  | symtab_popl_exp scope (BinOp {attr,opr,lhs,rhs}) =
	     (BinOp {attr=attr,opr=opr,lhs=symtab_popl_exp scope lhs,
							rhs=symtab_popl_exp scope rhs})
	  | symtab_popl_exp scope (Constraint {attr,exp,ty}) =
	     (Constraint {attr=attr,exp=symtab_popl_exp scope exp,ty=ty})
	  | symtab_popl_exp scope (Fn {attr=attr,match=match,symtab}) =
	     (Fn {attr=attr,
						 match=map (fn (x,y) =>
						 	(symtab_popl_pat symtab x,
							 symtab_popl_exp symtab y)) match,
							 symtab=symtab})
	  | symtab_popl_exp scope (If {attr,cond,tbr,fbr}) =
	  	 (If {attr=attr,
						 cond=symtab_popl_exp scope cond,
						 tbr=symtab_popl_exp scope tbr,
						 fbr=symtab_popl_exp scope fbr})
	  | symtab_popl_exp scope (Let {attr,decs,exp,symtab}) =
	  	 (Let {attr=attr,
						  decs=symtab_popl_decs symtab decs,
						  exp=symtab_popl_exp symtab exp,
						  symtab=symtab})
	  | symtab_popl_exp scope (Var {attr,name,symtab}) =
	  	 (Var {attr=attr,
		 	   name=name,
			   symtab=scope})
	  | symtab_popl_exp scope x =  x
	and symtab_popl_binds scope x = map (symtab_popl_bind scope) x
	and symtab_popl_bind scope (ValBind (p,e)) =  
			     (ValBind (symtab_popl_pat scope p,
				  		   symtab_popl_exp scope e))
	  | symtab_popl_bind scope (tb as TypeBind 
	  							{def,tycon=VarTy (sym,symtab),tyvars}) = 
	  	let
			val _ = Symtab.insert_t scope sym (SOME def,NONE)
		in
			tb
		end
	  | symtab_popl_bind scope x = x
	and symtab_popl_match scope x = x
	and symtab_popl_pat scope (AsPat (l,r)) = 
			AsPat (symtab_popl_pat scope l, symtab_popl_pat scope r)
	  | symtab_popl_pat scope (ConstraintPat (p,t)) =
	  		ConstraintPat (symtab_popl_pat scope p, t)
	  | symtab_popl_pat scope (AppPat l) =
	  		AppPat (map (symtab_popl_pat scope) l)
	  | symtab_popl_pat scope (VarPat {attr,name,symtab}) =
	  	let
			val _ = Symtab.insert_v scope name (NONE,NONE)
		in
	  		VarPat {attr=attr,name=name,symtab=scope}
		end
	  | symtab_popl_pat scope (OpPat {attr,symbol,symtab}) =
	  		OpPat {attr=attr,symbol=symbol,symtab=Symtab.top_level}
	  | symtab_popl_pat scope (TuplePat l) =
	  		TuplePat (map (symtab_popl_pat scope) l)
	  | symtab_popl_pat scope (ListPat l) =
	  		ListPat (map (symtab_popl_pat scope) l)
	  | symtab_popl_pat scope x = x
	and symtab_popl_clauses scope c = (map (symtab_popl_clause scope) c)
	and symtab_popl_clause scope {pats,resultType,body} =
		{pats=map (symtab_popl_pat scope) pats,
						resultType=resultType,
						body=symtab_popl_exp scope body}
	val symtab_popl = symtab_popl_decs

	fun translate _ prog = symtab_popl Symtab.top_level prog

end

