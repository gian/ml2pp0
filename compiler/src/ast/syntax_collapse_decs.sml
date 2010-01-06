structure SyntaxCollapseDecs : SYNTAX_PASS =
struct
	type syntax_pass_param = unit

	open Ast


	(* The expression e must already have had collapse_exp
	   applied to it.
	   
	   patToSt takes a pattern and returns a list of 
	   tuples:
	   	symbol * (exp -> exp) * ty option * symtab

	   the function, when applied to an expression
	   returns that argument appropriately transformed
	   in order to be that pattern, e.g.:

		val (a,b) = E

		[
			(a, fn x => #1 x))
			(b, fn x => #2 x))
		]

		The symtab is the appropriate symbol table into which to
		place the binding.
	   *)

	fun collect_terms t = []

	fun tup_ins symtab t e =
		let
			val terms = collect_terms t
		in
			List.app (
				fn term => 
				let
					val st = ref (Symtab.symtab ())
				in
					Symtab.insert_v symtab term
					(NONE,SOME (App {attr=[],
						  	exps=[
								Fn {attr=[],
									match = [(t,
										Var {attr=[],
											 name=term,
											 symtab=st
										})],
									symtab=st
									}
						  	]
						  }
					))
				end
				) terms
		end




	(* Remove all declarations by substituting them into the
	   appropriate symbol tables instead *)
	fun collapse_decs scope x = 
		map (fn k => (collapse_dec scope k)) x
	and collapse_dec scope (ExpDec {attr,exp}) = 
	  	raise Fail "ExpDec node present at SyntaxCollapseDecs"
	  | collapse_dec scope (NullDec) =  NullDec
	  | collapse_dec scope (LocalDec {attr,dec1,dec2,symtab}) =
	  	raise Fail "LocalDec not implemented"
	  | collapse_dec scope (ValDec {attr,tyvars,valBind,recBind}) =
		let
			val _ = collapse_binds scope valBind
			val _ = collapse_binds scope recBind
		in
			NullDec
		end
	  | collapse_dec scope (FunDec {attr,tyvars,clauses}) =
	  		raise Fail 
				"FunDec present after SyntaxFundecAnon should have run"
	  | collapse_dec scope (TypeDec {attr,tyBind}) =
	  	 (collapse_binds scope tyBind; NullDec)
	  | collapse_dec scope (fd as FixDec {attr,fixity,ops,symtab}) =
	  		NullDec
	  | collapse_dec scope x =  
	  		raise Fail "Unhandled declaration in SyntaxCollapseDecs"
	and collapse_exp scope (Handle {attr,exp,match}) = 
		 (Handle {attr=attr, 
							 exp=collapse_exp scope exp,
							 match=match})
	  | collapse_exp scope (App {attr,exps}) =
	     (App {attr=attr,exps=map (collapse_exp scope) exps})
	  | collapse_exp scope (BinOp {attr,opr,lhs,rhs}) =
	     (BinOp {attr=attr,opr=opr,lhs=collapse_exp scope lhs,
							rhs=collapse_exp scope rhs})
	  | collapse_exp scope (Constraint {attr,exp,ty}) =
	     (Constraint {attr=attr,exp=collapse_exp scope exp,ty=ty})
	  | collapse_exp scope (Fn {attr=attr,match=match,symtab}) =
	     (Fn {attr=attr,
						 match=map (fn (x,y) =>
						 	(x,
							 collapse_exp symtab y)) match,
							 symtab=symtab})
	  | collapse_exp scope (If {attr,cond,tbr,fbr}) =
	  	 (If {attr=attr,
						 cond=collapse_exp scope cond,
						 tbr=collapse_exp scope tbr,
						 fbr=collapse_exp scope fbr})
	  | collapse_exp scope (Let {attr,decs,exp,symtab}) =
	  	 (Let {attr=attr,
						  decs=collapse_decs symtab decs,
						  exp=collapse_exp symtab exp,
						  symtab=symtab})
	  | collapse_exp scope (Var {attr,name,symtab}) =
	  	 (Var {attr=attr,
		 	   name=name,
			   symtab=scope})
	  | collapse_exp scope x =  x
	and collapse_binds scope x = map (collapse_bind scope) x
	and collapse_bind scope (ValBind (p,e)) =  
		let
			val e' = collapse_exp scope e
			val p' = (case p of 
				VarPat {attr,name,symtab} =>
					Symtab.insert_v symtab name (NONE,SOME e')
			  | OpPat {attr,symbol,symtab} =>
			  		Symtab.insert_v symtab symbol (NONE,SOME e')
			  | TuplePat l => tup_ins scope p e'
			  | ListPat l => tup_ins scope p e'
			  | AppPat l => raise Fail "Not implemented" 
			  | AsPat (l,r) => raise Fail "Not implemented"
			  | ConstraintPat (p,t) => raise Fail "Not implemented"
			)
		
		in
			()
		end
	  | collapse_bind scope x = raise Fail "Unimplemented non-ValBind"

	fun translate _ prog = collapse_decs Symtab.top_level prog

end

