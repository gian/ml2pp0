signature SYMTAB =
sig
	type symbol_data

	type 'a symtab

	val symtab : symbol_data symtab ref -> symbol_data symtab 
	val empty : unit -> symbol_data symtab

	val basis : symbol_data symtab ref
	val top_level : symbol_data symtab ref

	type symtab_t

	val get_parent : symtab_t -> symtab_t
	val set_parent : symtab_t -> symtab_t -> symtab_t

	val insert_t : symtab_t -> Symbol.symbol -> symbol_data -> unit
	val insert_v : symtab_t -> Symbol.symbol -> symbol_data -> unit
	val insert_vi : symtab_t -> Symbol.symbol -> symbol_data -> unit

	val lookup_t : symtab_t -> Symbol.symbol -> symbol_data 
	val lookup_v : symtab_t -> Symbol.symbol -> symbol_data

	val print_scope : symtab_t -> unit
end


structure Symtab : SYMTAB =
struct

	type symbol_data = (Ast.ty option) * (Ast.ast option)

	type 'a symtab = {venv : 'a Symbol.table ref,
				      tenv : 'a Symbol.table ref,
					  iter_order : Symbol.symbol list ref}
  
 	type symtab_t = symbol_data symtab ref


	fun symtab parent = 
		let
			val e = Symbol.enter (Symbol.empty,
						Symbol.symbol "__parent_scope",
						(NONE, 
						 SOME (Ast.Node (Ast.Var (Symbol.symbol "__parent_scope"),
												  NONE,
												  parent,
												  [])
									  )))
		in
			{venv = ref e, 
	    	 tenv = ref Symbol.empty,
			 iter_order = ref []} 
		end

	fun empty () = {venv = ref Symbol.empty, 
					tenv = ref Symbol.empty,
					iter_order = ref []}

	val basis = ref ({venv=ref Symbol.empty, 
						  tenv= ref Symbol.empty,
						  iter_order = ref []}) : symtab_t

	val top_level = ref (symtab basis)
	val _ = let
				val iter_order = #iter_order (!top_level)
			in
				iter_order := []
			end


	fun insert_t scope s d =
		let
			val {venv,tenv,iter_order} = !scope
			val _ = tenv := Symbol.enter (!tenv,s,d)
		in
			()
		end

	fun insert_v scope s d =
		let
			val {venv,tenv,iter_order} = !scope
			val _ = venv := Symbol.enter (!venv,s,d)
		in
			()
		end


	(* Insert with iteration order update *)
	fun insert_vi scope s d =
		let
			val {venv,tenv,iter_order} = !scope
			val _ = insert_v scope s d
			val _ = if not (List.exists (fn x => s = x) (!iter_order)) 
					then
						iter_order := !iter_order @ [s] 
					else
						()
		in
			()
		end

	exception NoParent

	fun get_parent (scope : symtab_t) =
			let val {venv,tenv,iter_order} = !scope in
			(case Symbol.look (!venv, 
							   Symbol.symbol "__parent_scope")
				of SOME (_, SOME (Ast.Node (_,_,st,_))) => st 
				 | NONE => raise NoParent
				 | _ => raise Fail "invalid __parent_scope")
			end

	fun set_parent par scope =
		let
			val {venv,tenv,iter_order} = !scope
			val _ = venv := Symbol.enter (!venv,
								Symbol.symbol "__parent_scope",
									(NONE,
									 SOME (
									 	Ast.Node (Ast.Var (Symbol.symbol "__parent_scope"),
												  NONE,
												  par,
												  [])
									  )))
		in
			scope
		end

	fun lookup_v (scope : symtab_t) s =
		(case Symbol.look (!(#venv (!scope)), s) of
		    SOME v => v
		  | NONE => ((lookup_v (get_parent scope) s) handle NoParent =>
					raise Fail ("Unknown symbol '" ^ 
							Symbol.toString s ^ "'")))

	fun lookup_t scope s =
		(case Symbol.look (!(#tenv (!scope)), s) of
		    SOME v => v
		  | NONE => ((lookup_t (get_parent scope) s) handle NoParent =>
					raise Fail ("Unknown type '" ^ 
							Symbol.toString s ^ "'")))

	fun print_env env = 
		let
			val keys = Symbol.keys env
		
			fun prt NONE = "\t\tType: NONE\n"
			  | prt (SOME (x : Ast.ty)) = "\t\tType: " ^ PrettyPrint.ppty x ^ "\n"

			fun pra NONE = "\t\t AST: NONE\n"
			  | pra (SOME (x : Ast.ast)) = "\t\t AST: " ^ PrettyPrint.ppexp x ^ "\n"

			fun pr NONE _ = print "\tunrecognised symbol\n"
			  | pr (SOME s) (t,a) = 
			  		print ("\t"^ Symbol.toString s ^ ":\n" ^
						prt t ^
						pra a
					)
		in
			List.app (fn (x,(t,a)) => pr (Symbol.unhash x) (t,a)) keys
		end
			
	fun print_scope scope =
		let
			val {venv,tenv,iter_order} = !scope
			val _ = print "* Value Environment:\n"
			val _ = print_env (!venv) 
			val _ = print "* Type Environment:\n"
			val _ = print_env (!tenv)
			val _ = print "* Iteration Order:\n"
			val _ = print (String.concatWith ", " 
							(List.map Symbol.toString (!iter_order)
						))

			val _ = print "\n\n"
		in () end


end

