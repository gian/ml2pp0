structure BuiltIns =
struct

(*	fun builtin s t1 t2 = Symtab.insert_v Symtab.basis
		(Symbol.fromString s)
		(SOME (Ast.ArrowTy(t1,t2)), SOME (Ast.Node(Ast.BuiltIn (s, 
										Ast.ArrowTy (t1,t2)),
										NONE,
										Symtab.basis,
										[]))

	fun builtin_c s t1 v = Symtab.insert_v Symtab.basis 
		(Symbol.fromString s)
		(SOME t1, SOME v)

	val _ = (builtin "puts" Types.tyString Types.tyInt)
	val _ = (builtin "hd" (Ast.ListTy (Ast.PolyTy 0)) (Ast.PolyTy 0))
	val _ = (builtin "tl" (Ast.ListTy (Ast.PolyTy 0)) 
								(Ast.ListTy (Ast.PolyTy 0)))
	val _ = (builtin_c "nil" (Ast.ListTy (Ast.PolyTy 0)) 
							 	(Ast.Node (List,SOME (Ast.ListTy (Ast.PolyTy 0)),Symtab.basis, [])))*)

end
