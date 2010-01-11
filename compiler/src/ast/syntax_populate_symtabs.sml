structure SyntaxPopulateSymtabs : SYNTAX_PASS =
struct
	type syntax_pass_param = unit

	open Ast

	val ut = ref 10000
	fun mkFresh () = UVar (ut := !ut + 1; !ut)
	
	(* Do a pass over the AST and populate symtab fields appropriately *)
	fun symtab_popl_decs scope x = 
		map (fn k => (symtab_popl_dec scope k)) x
	and symtab_popl_dec scope (e as ExpDec exp) = 
	  	 (ExpDec (symtab_popl_exp scope exp))
	  | symtab_popl_dec scope (ValDec {tyvars,valBind,recBind}) =
	     (ValDec {tyvars=tyvars,
				  valBind=symtab_popl_binds scope valBind,
				  recBind=symtab_popl_binds scope recBind})
	  | symtab_popl_dec scope (FunDec (tyvars,clauses)) =
	  	 (FunDec (tyvars, map (symtab_popl_clauses scope) clauses))
	  | symtab_popl_dec scope (TypeDec tyBind) =
	  	 (TypeDec (symtab_popl_binds scope tyBind))
	  | symtab_popl_dec scope (fd as FixDec (fixity,ops,symtab)) =
	  	 fd
	  | symtab_popl_dec scope x =  x
	and symtab_popl_exp scope (Node(Fn,t,st,ch)) =
		let
			val newst = ref (Symtab.symtab scope)
		in
			Node (Fn,t,newst,map (symtab_popl_exp newst) ch)
		end
	  | symtab_popl_exp scope (Node(Let decs,t,symtab,ch)) =
	  	let
			val newst = ref (Symtab.symtab scope)
		in
	  	 	Node(Let (symtab_popl_decs newst decs),t,newst,ch)
		end
	  | symtab_popl_exp scope (Node(VarPat name,t,_,ch)) =
	  	let
			val _ = Symtab.insert_v scope name (t,NONE)
		in
	  		Node(VarPat name,t,scope,ch)
		end
	  | symtab_popl_exp scope (Node(l,t,symtab,ch)) = 
			Node(l,t,scope,map (symtab_popl_exp scope) ch)
	and symtab_popl_binds scope x = map (symtab_popl_bind scope) x
	and symtab_popl_bind scope (ValBind (p,e)) =  
			     (ValBind (symtab_popl_exp scope p,
				  		   symtab_popl_exp scope e))
	  | symtab_popl_bind scope (tb as TypeBind 
	  			{def,tycon=VarTy sym,tyvars}) = 
	  	let
			val _ = Symtab.insert_t scope sym (SOME def,NONE)
		in
			tb
		end
	  | symtab_popl_bind scope x = x
	and symtab_popl_clauses scope c = (map (symtab_popl_clause scope) c)
	and symtab_popl_clause scope {pats,resultType,body} =
		{pats=map (symtab_popl_exp scope) pats,
						resultType=resultType,
						body=symtab_popl_exp scope body}
	val symtab_popl = symtab_popl_decs

	fun translate _ prog = symtab_popl Symtab.top_level prog

end

