structure SyntaxTypeConv : SYNTAX_PASS =
struct
	(* Convert type names (that are just symbols)
	   to the built-in types that we know *)

	structure A = Ast

	fun id x = x

	type syntax_pass_param = unit

	fun lh l = hd (List.rev l)
	fun ltl l = List.rev (tl (List.rev l))

	fun typeconv (A.VarTy s) =
		(case Symbol.toString s of
			"int" => A.IntTy
		  | "string" => A.StringTy
		  | "bool" => A.BoolTy
		  | "real" => A.RealTy
		  | "char" => A.CharTy
		  | "word" => A.WordTy
		  | s' => 
		  	if String.isPrefix "'" s' then
				A.PolyTy (Char.ord (String.sub (s',1)) - Char.ord #"a")
			else A.VarTy s)
	  | typeconv (A.TyConTy (t, [])) = t
	  | typeconv (tc as A.TyConTy (A.VarTy t1, t2)) =
	  	(case Symbol.toString t1 of
			"vector" => A.VectorTy (typeconv (A.TyConTy (lh t2, ltl t2)))
		  | "list"   => A.ListTy (typeconv (A.TyConTy (lh t2, ltl t2)))
		  | _ => tc)
	  | typeconv k = k

	fun translate _ prog =
		AstOps.ast_map {decfun=id,
						expfun=id,
						bindfun=id,
						tyfun=typeconv,
						oprfun=id,
						clausesfun=id,
						clausefun=id} prog
end
