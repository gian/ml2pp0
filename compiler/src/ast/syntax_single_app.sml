structure SyntaxSingleApp : SYNTAX_PASS =
struct
	structure A = Ast

	fun id x = x

	type syntax_pass_param = unit

	fun single_app (A.App {attr,exps=[e]}) = e
	  | single_app k = k

	fun single_papp (A.AppPat [p]) = p
	  | single_papp k = k
	
	fun translate _ prog =
		AstOps.ast_map {decfun=id,
						expfun=single_app,
						patfun=single_papp,
						bindfun=id,
						tyfun=id,
						oprfun=id,
						clausesfun=id,
						clausefun=id} prog
end
