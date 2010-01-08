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

	fun collect_terms (AsPat (p1,p2)) = 
			collect_terms p1 @ collect_terms p2
	  | collect_terms (ConstraintPat (p,t)) = 
	  		collect_terms p
	  | collect_terms (AppPat []) = []
	  | collect_terms (AppPat (h::t)) = 
	  		collect_terms h @ collect_terms (AppPat t)
	  | collect_terms (VarPat {attr,name,symtab}) = [name]
	  | collect_terms (TuplePat []) = []
	  | collect_terms (TuplePat (h::t)) =
	  		collect_terms h @ collect_terms (TuplePat t)
	  | collect_terms (ListPat []) = []
	  | collect_terms (ListPat (h::t)) =
			collect_terms h @ collect_terms (ListPat t)
	  | collect_terms _ = []

	val pm_rhs = ref 0

	fun tup_ins symtab t (SOME e) =
		let
			val terms = collect_terms t

			val es = Symbol.fromString 
				("_pm_rhs_" ^ Int.toString (!pm_rhs))
			val _ = pm_rhs := !pm_rhs + 1
			val _ = Symtab.insert_v symtab es (NONE,SOME e)
			val e' = Var {attr=[],name=es,symtab=symtab}
		in
			List.app (
				fn term => 
				let
					val st = ref (Symtab.symtab symtab)
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
									},
								e'
						  	]
						  }
					))
				end
				) terms
		end
	  | tup_ins symtab t NONE = raise Fail "tup_ins got NONE for expression"

	val wv = ref 100

	fun mkUnique () = 
		Symbol.fromString ("__wild_" ^ Int.toString (wv := !wv +1; !wv))

	fun patToSt scope p e' =
		(case p of 
				VarPat {attr,name,symtab} =>
					let
						val _ = Symtab.insert_v scope name (NONE,e')
					 	val pat' = VarPat {attr=attr,name=name,symtab=scope}
					in
						pat'
					end
			  | OpPat {attr,symbol,symtab} =>
			  		(Symtab.insert_v symtab symbol (NONE,e'); p)
					(* FIXME *)
			  | TuplePat l => (tup_ins scope p e'; p)
			  | ListPat l => (tup_ins scope p e'; p)
			  | AppPat l => raise Fail "Not implemented AppDec" 
			  | AsPat (l,r) => raise Fail "Not implemented AsPat"
			  | ConstraintPat (p,t) => raise Fail "Not implemented cons"
			  | WildPat => 
			  		(Symtab.insert_v scope (mkUnique()) (NONE,e'); p)
			  | p' => raise Fail ("Unimplemented in patToSt" ^ PrettyPrint.pppat p')
			)


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
	  	let
			val sc = ref (Symtab.symtab scope)

			val f = (Fn {attr=attr,
						 match=map (fn (x,y) => (
						 	(patToSt sc x NONE,
							 collapse_exp sc y))) match,
							 symtab=sc})
		in
			f
	     end
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
			val _ = patToSt scope p (SOME e')	
		in
			()
		end
	  | collapse_bind scope (ValRecBind (p,m)) = 
	  	let
			val sc = ref (Symtab.symtab scope)
			val m' = map (fn (pat,exp) => (
			pat,collapse_exp sc exp)) m
			val e' = Fn {attr=[],match=m',symtab=sc}
			val _ = patToSt scope p (SOME e')
		in
			()
		end
	  | collapse_bind scope (TypeBind _) = () (* already bound *)
	  | collapse_bind scope x = raise Fail "Unimplemented non-ValBind"

	fun translate _ prog = collapse_decs Symtab.top_level prog

end

