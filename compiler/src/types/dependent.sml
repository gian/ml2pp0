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


	fun dep_ty_fn (A.ArrowTy (t1,t2)) m =
		let
			val _ = ()
		in
			A.DepTy (A.ArrowTy (t1,t2), int_node 1)
		end

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
					val e' = AstOps.ast_map_exp 
											{decfun=id,
											 expfun=(fn x => #1 (dep_ty x)),
											 bindfun=id,
											 tyfun=id,
											 oprfun=id,
											 clausesfun=id,
											 clausefun=id} e
					
					val (A.Node(_,t',_,_)) = e'

					val _ = print ("[dep term: " ^ PrettyPrint.ppexp e' ^ "]\n")
					val _ = upd ve s (t', SOME e')
				in
					()
				end
			  | (s,(t,NONE)) => ()) vkeys
		end


end
