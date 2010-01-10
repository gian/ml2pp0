structure BuiltIns =
struct

	fun builtin s t1 t2 = Symtab.insert_v Symtab.top_level
		(Symbol.fromString s)
		(SOME (Ast.ArrowTy(t1,t2)), SOME (Ast.BuiltIn (s, 
										Ast.ArrowTy (t1,t2))))

	fun builtin_c s t1 v = Symtab.insert_v Symtab.top_level 
		(Symbol.fromString s)
		(SOME t1, SOME v)

	val _ = (builtin "puts" Types.tyString Types.tyInt)
	val _ = (builtin "hd" (Ast.ListTy (Ast.PolyTy 0)) (Ast.PolyTy 0))
	val _ = (builtin "tl" (Ast.ListTy (Ast.PolyTy 0)) 
								(Ast.ListTy (Ast.PolyTy 0)))
	val _ = (builtin_c "nil" (Ast.ListTy (Ast.PolyTy 0)) 
							 	(Ast.List {attr=[],exps=[]}))

end
