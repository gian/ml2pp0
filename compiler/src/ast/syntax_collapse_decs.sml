structure SyntaxCollapseDecs : SYNTAX_PASS =
struct
	type syntax_pass_param = unit

	open Ast

	val uv = ref 8000
	fun nextuv () = UVar (uv := !uv + 1; !uv)

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

	  fun collect_terms (Node (VarPat name,_,_,_)) = [name]
	    | collect_terms (Node (_,_,_,ch)) = 
			List.foldl (fn (a,b) => b @ collect_terms a ) [] ch

	val pm_rhs = ref 0

(*	fun tup_ins symtab t (SOME e) =
		let
			val terms = collect_terms t

			val es = Symbol.fromString 
				("_pm_rhs_" ^ Int.toString (!pm_rhs))
			val _ = pm_rhs := !pm_rhs + 1
			val _ = Symtab.insert_vi symtab es (NONE,SOME e)
			val e' = Var es
		in
			List.app (
				fn term => 
				let
					val st = ref (Symtab.symtab symtab)
				in
					Symtab.insert_vi symtab term
					(NONE,SOME (App {attr=[],
						  	exps=[
								Fn {attr=[],
									match = [(t,
										Var 
											 name=term,
											 symtab=st
										})],
									symtab=st,
									ty = SOME (nextuv()) 
									},
								e'
						  	]
						  }
					))
				end
				) terms
		end
	  | tup_ins symtab t NONE = raise Fail "tup_ins got NONE for expression"*)

	fun tup_ins symtab t _ = raise Fail "not implemented tup_ins"

	val wv = ref 100

	fun mkUnique () = 
		Symbol.fromString ("__wild_" ^ Int.toString (wv := !wv +1; !wv))

	fun patToSt scope p e' =
		(case p of 
				VarPat name =>
					let
						val _ = Symtab.insert_vi scope name (NONE,e')
					 	val pat' = VarPat name
					in
						pat'
					end
			  | OpPat symbol =>
			  		(Symtab.insert_vi scope symbol (NONE,e'); p)
					(* FIXME *)
			  | TuplePat => (tup_ins scope p e'; p)
			  | ListPat => (tup_ins scope p e'; p)
			  | AppPat => raise Fail "Not implemented AppDec" 
			  | AsPat => raise Fail "Not implemented AsPat"
			  | ConstraintPat t => raise Fail "Not implemented cons"
			  | WildPat => 
			  		(Symtab.insert_vi scope (mkUnique()) (NONE,e'); p)
			  | p' => raise Fail ("Unimplemented in patToSt" ^ PrettyPrint.ppast p')
			)


	(* Remove all declarations by substituting them into the
	   appropriate symbol tables instead *)
	
	fun translate _ prog =
		let
				fun id x = x

				fun cb (ValBind (p as Node(x,_,scope,_),e)) =  
				let
					val _ = patToSt scope x (SOME e)	
				in
					ValBind (p,e)	
				end
			  | cb (ValRecBind (p as Node(x,_,scope,_),m)) = 
				let
					val st = ref (Symtab.symtab scope)

					fun setst (x as Node (Fn,_,_,_)) = x
					  | setst (x as Node (Let _,_,_,_)) = x
					  | setst (Node (s,t,_,c)) = Node (s,t,st,map setst c)

					val e' = Node(Fn,NONE,st,map setst m)

					val _ = patToSt scope x (SOME e') 
				in
					ValRecBind(p,m)
				end
			  | cb (TypeBind x) = TypeBind x (* already bound *)
			  | cb x = raise Fail "Unimplemented non-ValBind"
		in
			AstOps.ast_map {
				decfun = (fn x => NullDec),
				expfun = id,
				bindfun = cb,
				tyfun = id,
				oprfun = id,
				clausesfun = id,
				clausefun = id
			} prog
		end

	
end

