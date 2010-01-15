structure SyntaxClosureConv : SYNTAX_PASS =
struct
	structure A = Ast

	type syntax_pass_param = unit

	fun translate _ prog = prog
end
