structure Types =
struct
	val tyInt = Ast.VarTy (Symbol.fromString "int")
	val tyWord = Ast.VarTy (Symbol.fromString "word")
	val tyReal = Ast.VarTy (Symbol.fromString "real")
	val tyString = Ast.VarTy (Symbol.fromString "string")
	val tyChar = Ast.VarTy (Symbol.fromString "char")
	val tyBool = Ast.VarTy (Symbol.fromString "bool")

end
