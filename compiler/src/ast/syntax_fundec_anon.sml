structure SyntaxFundecAnon : SYNTAX_PASS =
struct
	structure A = Ast

	fun id x = x
 
	type syntax_pass_param = unit
 
	fun onep [] = raise Fail "Empty pattern"
	  | onep [f] = raise Fail "fun declaration without pattern"
	  | onep [f1,f2] = f2
	  | onep (h::t) = A.Node (A.AppPat,NONE,Symtab.top_level,t)
	 (* FIXME should we turn curried functions into multiple
	 	nested anonymous functions here? *)
 
	fun onecl {pats,resultType=NONE,body} =	
		A.Node(A.Match, NONE, Symtab.top_level, [onep pats, body])
      | onecl {pats,resultType=SOME t,body} = 
		A.Node(A.Match, NONE, Symtab.top_level, [onep pats, body])
		(* FIXME: Set an ArrowTy type of ?Xn -> t *)

	fun onefn cl =
		let
			val fc = hd cl
		in
			A.ValRecBind (hd (#pats fc),
						map onecl cl)
		end
 
	fun dec (A.FunDec (tyvars,clauses)) = 
		let
			val _ = print ("FunDec: " ^ Int.toString (length clauses) ^ "\n")
			val fns = map onefn clauses	
			
			val _ = print ("FunDec fns: " ^ Int.toString (length fns) ^ "\n")
		in
			A.ValDec {tyvars=tyvars,
					  valBind=[],
					  recBind=fns}
		end
	  | dec x = x

	type syntax_pass_param = unit

	fun translate _ prog = AstOps.ast_map {
								decfun = dec,
								expfun = id,
								bindfun = id,
								tyfun = id,
								oprfun = id,
								clausesfun = id,
								clausefun = id
							} prog

end
