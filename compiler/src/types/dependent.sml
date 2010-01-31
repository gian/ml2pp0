structure Dependent =
struct
	structure A = Ast

	fun equal (A.Node(A.Int i,_,_,_), A.Node (A.Int j,_,_,_)) =
		i <= j
	  | equal (x,y) =
	  	let
			val _ = print ("DEPENDENT: " ^ PrettyPrint.ppexp x ^ " < " ^ PrettyPrint.ppexp y ^ "\n")
		in
			true
		end

	fun int_node i = A.Node (A.Int i, SOME A.IntTy, Symtab.top_level, [])

	fun check_dep_subty (A.Node (A.Var _,_,_,_)) _ = true
	  | check_dep_subty (A.Node (A.Int i,_,_,_)) (A.Node(A.Int j,_,_,_)) =
	  	i <= j
	  | check_dep_subty (A.Node (_,_,_,ch)) (A.Node(_,_,_,ch')) =
	  	let
			val ch'' = ListPair.zip (ch,ch')
		in
			List.all (fn x => x) (map (fn (a,b) => check_dep_subty a b) ch'')
		end
	  | check_dep_subty e1 e2 = raise Fail 
	  		("Not implemented: " ^ PrettyPrint.ppexp e1 ^ " <= " ^
				PrettyPrint.ppexp e2)

	fun strip_dep (A.DepTy (t,e)) = 
		let
			val _ = print ("Stripping: " ^ PrettyPrint.ppty t ^ "!" ^ PrettyPrint.ppexp e ^ "\n")
		in
			strip_dep t
		end
	  | strip_dep t = 
	  	let
			val _ = print ("Strip returning: " ^ PrettyPrint.ppty t ^ "\n")
		in
			t
		end

	fun mkdep (A.DepTy (t,_)) e = A.DepTy (t,e)
	  | mkdep t e = A.DepTy (t,e)

	fun subst_dep (A.Node(A.Var s,_,_,_)) out arg = 
		let
			val _ = print ("subst_dep: " ^ Symbol.toString s ^ "\n")
			val r = AstOps.substinexp (A.Var s) out arg
			val _ = print ("subst_dep out: " ^ PrettyPrint.ppexp r ^ "\n")
		in
			r
		end
	  | subst_dep (n1 as A.Node(a,b,c,ch)) out (A.Node(a',b',c',ch')) =
	  	let
			val _ = print ("subst_dep n1: " ^ PrettyPrint.ppexp n1 ^ "\n")
			val ch'' = ListPair.zip (ch,ch')
		in
			List.foldl (fn ((c1,c2),b) => subst_dep c1 b c2) out ch''
		end
	  | subst_dep _ out _ = out

	fun dep_ty_fn (A.ArrowTy (t1,t2)) m =
		let
			val _ = ()
		in
			A.DepTy (A.ArrowTy (t1,t2), int_node 1)
		end

	fun get_dep' (A.DepTy (t,e)) = e
	  | get_dep' _ = A.Node(A.Int 1,SOME A.IntTy,Symtab.top_level,[])

	fun get_dep (A.Node(_,SOME t,_,_)) = get_dep' t
	  | get_dep (A.Node(_,NONE,_,_)) = raise Fail ("get_dep called on untyped")

	fun dep_ty (A.Node(A.Vector,SOME t,x,l)) =
		let
			val t' = A.DepTy (t, int_node (length l))
		in
			(A.Node(A.Vector,SOME t',x,l), t')
		end
	  | dep_ty (A.Node(A.List,SOME t,x,l)) = 
		let
			val t' = A.DepTy (t, int_node (length l))
		in
			(A.Node(A.List,SOME t',x,l), t')
		end	
	  | dep_ty (A.Node(A.Fn,SOME t,x,m)) = 
	  	let
			val t' = dep_ty_fn t m
		in
			(A.Node(A.Fn,SOME t',x,m), t')
		end
	  | dep_ty (A.Node(A.App,t,x,[tm1,tm2])) =
	  	let
			fun s (A.Node(a,SOME t,b,c)) = 
				A.Node (a,SOME (strip_dep t), b,c )

			val (tm1',t',tm2') = (case s tm1 of
				(A.Node(a,SOME (A.ArrowTy (it,rt)),b,c)) =>
				let
					val indep = get_dep' it (* input constraint *)
					val outdep = get_dep' rt (* output constraint *)
					val (tm2',tm2t') = dep_ty tm2
					val argdep = get_dep' tm2t'

					val _ = print ("indep: " ^ PrettyPrint.ppexp indep ^ "\n")
					val _ = print ("outdep: " ^ PrettyPrint.ppexp outdep ^ "\n")
					val _ = print ("argdep: " ^ PrettyPrint.ppexp argdep ^ "\n")

					(* First, check that any fixed constraints are met *)
					val _ = check_dep_subty indep argdep 
					(* Subsitute any free vars in the output *)
					val outdep' = subst_dep indep outdep argdep
					
					val _ = print ("outdep': " ^ PrettyPrint.ppexp outdep'^ "\n")
					
					val t'' = mkdep rt outdep'
				in
					(A.Node(a,SOME (A.ArrowTy (it,t'')),b,c),t'',tm2')
				end
				| e => raise Fail ("Non-arrow type application in dep_ty: " ^
									PrettyPrint.ppexp e))
		in
			(A.Node(A.App,SOME t',x,[tm1',tm2']), t')
		end
	  | dep_ty (A.Node(A.App,t,x,_)) =
		raise Fail ("Non two-valued app reached dep_ty")
	  | dep_ty (A.Node(A.Var s,t,symtab,l)) =
	  	let
			val (t',e') = Symtab.lookup_v symtab s
			val _ = print ("dep_ty: Var " ^ Symbol.toString s ^ " = " ^ 
				PrettyPrint.ppty (valOf t') ^ "\n")
		in
			(A.Node(A.Var s,t',symtab,l), valOf t')
		end
	  | dep_ty (n as A.Node(_,SOME (d as A.DepTy _),_,_)) = (n,d)
	  | dep_ty (A.Node(s,SOME t,x,l)) = 
	  	let
			val t' = A.DepTy (t, int_node 1)
		in
			(A.Node(s,SOME t',x,l),t')
		end
	  | dep_ty s = raise Fail ("Unhandled in dep_ty: " ^ PrettyPrint.ppexp s)

	fun check symtab =
		let
			val _ = print "[Dependent Type Checking]\n"
			val {venv=ve,tenv,iter_order} = !symtab

			fun upd env s (t,e) = 
			  		Symtab.insert_v symtab s (t,e)

			fun id x = x

			val vkeys = List.map (fn x => (x, Symtab.lookup_v symtab x))
							(!iter_order)

		in
			List.app (fn (s,(SOME t,SOME e)) =>
				if s = (Symbol.fromString "__parent_scope") 
				then () else
				let
					val _ = AstOps.noEnterDependentTypes ()
					val e' = AstOps.ast_map_exp 
											{decfun=id,
											 expfun=(fn x => #1 (dep_ty x)),
											 bindfun=id,
											 tyfun=id,
											 oprfun=id,
											 clausesfun=id,
											 clausefun=id} e
					
					val _ = AstOps.enterDependentTypes()

					val (A.Node(_,t',_,_)) = e'

					val _ = print ("[dep term: " ^ PrettyPrint.ppexp e' ^ "]\n")
					val _ = upd ve s (t', SOME e')
				in
					()
				end
			  | (s,(t,NONE)) => ()) vkeys
		end


end
