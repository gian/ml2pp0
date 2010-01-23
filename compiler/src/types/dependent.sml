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

	fun dep_ty (A.Node(A.Vector,SOME t,_,l)) = A.DepTy (t, int_node (length l))
	  | dep_ty (A.Node(A.List,SOME t,_,l)) = A.DepTy (t, int_node (length l))
	  | dep_ty (A.Node(A.Fn,SOME t,_,m)) = dep_ty_fn t m
	  | dep_ty (A.Node(_,SOME t,_,_)) = A.DepTy (t, int_node 1)

	fun check symtab =
		let
			val {venv=ve,tenv,iter_order} = !symtab

			fun upd env s (t,e) = 
			  		Symtab.insert_v symtab s (t,e)

			val vkeys = List.map (fn x => (x, Symtab.lookup_v symtab x))
							(!iter_order)

		in
			List.app (fn (s,(SOME t,SOME e)) =>
				if s = (Symbol.fromString "__parent_scope") 
				then () else
				let
					val t' = dep_ty e
					val _ = upd ve s (SOME t', SOME e)
				in
					()
				end
			  | (s,(t,NONE)) => ()) vkeys
		end


end
