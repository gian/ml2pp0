structure BuiltIns =
struct

	structure A = Ast

	fun builtin s t1 t2 = Symtab.insert_v Symtab.basis
		(Symbol.fromString s)
		(SOME (A.ArrowTy(t1,t2)), 
		 SOME (A.Node(
		 		A.BuiltIn
					(s,A.ArrowTy (t1,t2)),NONE,Symtab.basis,[])))

	fun builtin_c s t1 v = Symtab.insert_v Symtab.basis 
		(Symbol.fromString s)
		(SOME t1, SOME v)

	fun mkDep (t,e) = A.DepTy (t, e)

	val _ = (builtin "puts" Types.tyString Types.tyInt)
	val _ = (builtin "hd" (mkDep (A.ListTy (A.PolyTy 0), 
								  A.Node (A.Int 1,
								  			NONE,
											Symtab.top_level,
											[]))) (A.PolyTy 0))
	val _ = (builtin "tl" (mkDep(A.ListTy (A.PolyTy 0),
							A.Node (A.Var (Symbol.fromString "n"),
											   SOME A.IntTy,
											   Symtab.top_level,
											   [])
		
							))

							(mkDep(A.ListTy (A.PolyTy 0),
							A.Node (A.App,
									SOME A.IntTy,
									Symtab.top_level,
									[
										A.Node(A.Var (Symbol.fromString "-"),
											   NONE,
											   Symtab.basis,
											   []),
										A.Node(A.Tuple,
											   SOME (A.TupleTy [A.IntTy,A.IntTy]),
											   Symtab.top_level,
											   [
												A.Node(A.Var (Symbol.fromString "n"),
											   		   SOME A.IntTy,
											   		   Symtab.top_level,
											   		   []),
												A.Node(A.Int 1,
											   		   SOME A.IntTy,
											           Symtab.top_level,
											   		   [])
											   ])
									])
							))) 
	val _ = (builtin_c "nil" (A.ListTy (A.PolyTy 0)) 
							 	(A.Node (A.List,
									SOME (A.ListTy (A.PolyTy 0)),
									Symtab.basis, [])))
	val _ = builtin "print_int" Types.tyInt Types.tyInt
	val _ = builtin "input_int" A.IntTy A.IntTy
	val _ = builtin "print" Types.tyString Types.tyInt

	fun builtin_binop s a b c =
		builtin s 
			(A.TupleTy [a,b])
			c

	fun var_node s = 
		A.Node(A.Var (Symbol.fromString s), SOME A.IntTy, Symtab.top_level, [])

	val _ = builtin_binop "=" (A.PolyTy 0) (A.PolyTy 0) A.BoolTy 
	val _ = builtin_binop "+" A.IntTy A.IntTy A.IntTy 
	val _ = builtin_binop "-" A.IntTy A.IntTy A.IntTy 
	val _ = builtin_binop "*" A.IntTy A.IntTy A.IntTy 
	val _ = builtin_binop "div" A.IntTy A.IntTy A.IntTy 
	val _ = builtin_binop "mod" A.IntTy A.IntTy A.IntTy 
	val _ = builtin_binop "<" A.IntTy A.IntTy A.BoolTy 
	val _ = builtin_binop ">" A.IntTy A.IntTy A.BoolTy 
	val _ = builtin_binop "<>" A.IntTy A.IntTy A.BoolTy 
	val _ = builtin_binop ">=" A.IntTy A.IntTy A.BoolTy 
	val _ = builtin_binop "<=" A.IntTy A.IntTy A.BoolTy 
	val _ = builtin_binop "@" (A.DepTy(A.ListTy (A.PolyTy 0), var_node "n"))
							   (A.DepTy(A.ListTy (A.PolyTy 0), var_node "m"))
							   (A.DepTy(A.ListTy (A.PolyTy 0), 
									A.Node (A.App,
									SOME A.IntTy,
									Symtab.top_level,
									[
										A.Node(A.Var (Symbol.fromString "+"),
											   NONE,
											   Symtab.basis,
											   []),
										A.Node(A.Tuple,
											   SOME (A.TupleTy [A.IntTy,A.IntTy]),
											   Symtab.top_level,
											   [
											   	var_node "n",
											    var_node "m"
											   ])
									]))
								)


								
	val _ = builtin_binop "::" (A.PolyTy 0) 
							   (A.DepTy(A.ListTy (A.PolyTy 0), var_node "n"))
							   (A.DepTy(A.ListTy (A.PolyTy 0),
								A.Node (A.App,
									SOME A.IntTy,
									Symtab.top_level,
									[
										A.Node(A.Var (Symbol.fromString "+"),
											   NONE,
											   Symtab.basis,
											   []),
										A.Node(A.Tuple,
											   SOME (A.TupleTy [A.IntTy,A.IntTy]),
											   Symtab.top_level,
											   [
												A.Node(A.Var (Symbol.fromString "n"),
											   		   SOME A.IntTy,
											   		   Symtab.top_level,
											   		   []),
												A.Node(A.Int 1,
											   		   SOME A.IntTy,
											           Symtab.top_level,
											   		   [])
											   ])
									])
							))
end
