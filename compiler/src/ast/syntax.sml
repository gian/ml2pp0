structure Syntax =
struct
	structure A = Ast
	structure S = Symbol

	fun convOpr "+" = A.Plus
	  | convOpr "-" = A.Minus
	  | convOpr "*" = A.Times
	  | convOpr "div" = A.Div
	  | convOpr "/" = A.RDiv
	  | convOpr "^" = A.StrConcat
	  | convOpr "::" = A.Cons
	  | convOpr "@" = A.Concat
	  | convOpr "mod" = A.Mod
	  | convOpr "=" = A.Equal
	  | convOpr "<>" = A.NEqual
	  | convOpr "<" = A.LT
	  | convOpr ">" = A.GT
	  | convOpr "<=" = A.LTEqual
	  | convOpr ">=" = A.GTEqual
	  | convOpr ":=" = A.Assign
	  | convOpr "o" = A.Compose
	  | convOpr "before" = A.Before
	  | convOpr s = A.SOpr (S.fromString s)

	fun unflatten_ops prog =
	let
		val _ = print "UNFLATTEN\n"

		fun id x = x
		
		val infixes = ref [] : A.symbol list ref

		fun decfun (d as A.FixDec {attr,fixity=A.Infix _,ops}) =
			let
				val _ = print "DecFun"
				val _ = infixes := !infixes @ ops	
			in
				d
			end
		  | decfun x = x

		(* Collect infix definitions *)
		val _ = AstOps.ast_map {
			decfun = decfun,
			expfun = id,
			patfun = id,
			bindfun = id,
			tyfun = id,
			oprfun = id,
			clausesfun = id,
			clausefun = id
		} prog

		fun expfun k (d as A.App {attr,exps}) =
			let
				val _ = print "EXPFUN1\n"
				fun splitOnOp s lhs [] = A.App {attr=attr,exps=lhs}
				  | splitOnOp s lhs (h::t) =
				  	if (fn (A.Var {name=x,...}) => x = s | _ => false) h
					then 
						A.BinOp {attr=[], 
								 opr=convOpr (S.toString s), 
								 lhs=A.App {attr=[],exps=lhs}, 
								 rhs=splitOnOp s [] t}
					else
						splitOnOp s (lhs @ [h]) t
			in
				splitOnOp k [] exps
			end
		  | expfun k d =
				(print "EXPFUN1\n"; d)

		fun f k = {
			decfun = id,
			expfun = expfun k,
			patfun = id,
			bindfun = id,
			tyfun = id,
			oprfun = id,
			clausesfun = id,
			clausefun = id
		}
	in
		List.foldl (fn (k,p) => AstOps.ast_map (f k) p) prog (!infixes)
	end

end

