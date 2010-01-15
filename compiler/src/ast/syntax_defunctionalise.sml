structure SyntaxDefunctionalise : SYNTAX_PASS =
struct
	structure A = Ast

	fun id x = x

	type syntax_pass_param = unit

	fun translate _ prog = prog
end
