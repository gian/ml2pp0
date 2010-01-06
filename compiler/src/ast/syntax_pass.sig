signature SYNTAX_PASS =
sig
	type syntax_pass_param

	val translate : syntax_pass_param -> Ast.program -> Ast.program
end
