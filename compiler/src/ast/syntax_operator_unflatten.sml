structure SyntaxOperatorUnflatten : SYNTAX_PASS =
struct
	structure A = Ast
	structure S = Symbol

	type syntax_pass_param = unit

	open A

	fun convOpr s = (((fn (_,SOME e) => e
	                  | _ => raise Fail "Operator not found")
					  	(Symtab.lookup_v Symtab.basis 
							(S.fromString s))))
					 handle _ =>
			A.Node(A.Var (S.fromString s),NONE,Symtab.basis,[])

	fun translate _ prog =
	let
		fun id x = x
		
		val infixes = ref [
			S.fromString "*",
			S.fromString "/",
			S.fromString "mod",
			S.fromString "div",
			S.fromString "+",
			S.fromString "-",
			S.fromString "^",
			S.fromString "::",
			S.fromString "@",
			S.fromString "=",
			S.fromString "<>",
			S.fromString ">",
			S.fromString ">=",
			S.fromString "<",
			S.fromString "<=",
			S.fromString ":=",
			S.fromString "o",
			S.fromString "before"
		] : A.symbol list ref

		fun decfun (d as A.FixDec (A.Infix _,ops,st)) =
			let
				val _ = infixes := !infixes @ ops	
			in
				d
			end
		  | decfun x = x

		(* Collect infix definitions *)
		val _ = AstOps.ast_map {
			decfun = decfun,
			expfun = id,
			bindfun = id,
			tyfun = id,
			oprfun = id,
			clausesfun = id,
			clausefun = id
		} prog

		fun expfun k (A.Node(A.App,_,st,exps)) =
			let
				fun splitOnOp s lhs [] = A.Node(A.App,NONE,st,lhs)
				  | splitOnOp s lhs (h::t) =
				  	if (fn (A.Node(Var x,_,_,_)) => x = s | _ => false) h
					then 
						A.Node (A.App,  
								 NONE,
								 st,
								 [
								 	convOpr (S.toString s),
								 	A.Node(Tuple,
									NONE,
									st,
									[
										A.Node (A.App,NONE,st,lhs), 
								 		splitOnOp s [] t
									])
								 ])
					else
						splitOnOp s (lhs @ [h]) t
			in
				splitOnOp k [] exps
			end
		  | expfun k d = d

		fun f k = {
			decfun = id,
			expfun = k,
			bindfun = id,
			tyfun = id,
			oprfun = id,
			clausesfun = id,
			clausefun = id
		}

	in
		List.foldr (fn (k,p) => AstOps.ast_map 
			(f (expfun k)) p) prog (!infixes)
	end

end
