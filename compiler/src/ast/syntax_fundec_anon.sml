structure SyntaxFundecAnon : SYNTAX_PASS =
struct
	structure A = Ast

	fun id x = x

	type syntax_pass_param = unit

	fun onep [] = raise Fail "Empty pattern"
	  | onep [f] = raise Fail "fun declaration without pattern"
	  | onep [f1,f2] = f2
	  | onep (h::t) = A.AppPat t

	fun onecl {pats,resultType=NONE,body} =	(onep pats, body)
      | onecl {pats,resultType=SOME t,body} = 
	  	(onep pats, A.Constraint {attr=[],
								exp=body,
								ty=t})

	fun onefn cl =
		let
			val fc = hd cl
		in
			A.ValRecBind (hd (#pats fc),
						map onecl cl)
		end

	fun dec (A.FunDec {attr,tyvars,clauses}) = 
		let
			val fns = map onefn clauses	
		in
			A.ValDec {attr=[],
					tyvars=tyvars,
					valBind=[],
					recBind=fns}
		end
	  | dec x = x

	fun translate _ prog =
		AstOps.ast_map {decfun=dec,
						expfun=id,
						patfun=id,
						bindfun=id,
						tyfun=id,
						oprfun=id,
						clausesfun=id,
						clausefun=id} prog
end
