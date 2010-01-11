structure SyntaxSingleApp : SYNTAX_PASS =
struct
	structure A = Ast

	fun id x = x

	type syntax_pass_param = unit

	fun single_app (A.Node(A.App,_,_,[e])) = e
	  | single_app (A.Node(A.AppPat,_,_,[p])) = p
	  | single_app k = k

	fun translate _ prog =
		AstOps.ast_map {decfun=id,
						expfun=single_app,
						bindfun=id,
						tyfun=id,
						oprfun=id,
						clausesfun=id,
						clausefun=id} prog
end
