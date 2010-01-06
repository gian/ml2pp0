structure Types =
struct
	val tyInt = Ast.VarTy (Symbol.fromString "int", Symtab.top_level)
	val tyWord = Ast.VarTy (Symbol.fromString "word", Symtab.top_level)
	val tyReal = Ast.VarTy (Symbol.fromString "real", Symtab.top_level)
	val tyString = Ast.VarTy (Symbol.fromString "string", Symtab.top_level)
	val tyChar = Ast.VarTy (Symbol.fromString "char", Symtab.top_level)
	val tyBool = Ast.VarTy (Symbol.fromString "bool", Symtab.top_level)

end
