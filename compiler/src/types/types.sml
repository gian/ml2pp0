structure Types =
struct
	val tyInt = Ast.VarTy (Symbol.fromString "int", Symbol.top_level)
	val tyWord = Ast.VarTy (Symbol.fromString "word", Symbol.top_level)
	val tyReal = Ast.VarTy (Symbol.fromString "real", Symbol.top_level)
	val tyString = Ast.VarTy (Symbol.fromString "string", Symbol.top_level)
	val tyChar = Ast.VarTy (Symbol.fromString "char", Symbol.top_level)
	val tyBool = Ast.VarTy (Symbol.fromString "bool", Symbol.top_level)

end
