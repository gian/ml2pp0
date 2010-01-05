signature SYMTAB =
sig
	type symbol_data

	type 'a symtab

	val symtab : unit -> symbol_data symtab 
	
	val top_level : symbol_data symtab ref

	type symtab_t

	val insert_t : symtab_t -> Symbol.symbol -> symbol_data -> unit
	val insert_v : symtab_t -> Symbol.symbol -> symbol_data -> unit

	val print_scope : symtab_t -> unit
end


structure Symtab : SYMTAB =
struct

	type symbol_data = (Ast.ty option) * (Ast.exp option)

	type 'a symtab = {venv : 'a Symbol.table ref,
				            tenv : 'a Symbol.table ref}
  
 	type symtab_t = 
		{venv : symbol_data Symbol.table ref,
		 tenv : symbol_data Symbol.table ref} ref


	fun symtab () = {venv = ref Symbol.empty 
					, tenv = ref Symbol.empty} 

	val top_level = ref (symtab ())

	fun insert_t scope s d =
		let
			val {venv,tenv} = !scope
			val _ = tenv := Symbol.enter (!tenv,s,d)
		in
			()
		end

	fun insert_v scope s d =
		let
			val {venv,tenv} = !scope
			val _ = venv := Symbol.enter (!venv,s,d)
		in
			()
		end

	fun print_env env = 
		let
			val keys = Symbol.keys env
		
			fun prt NONE = "\t\tType: NONE\n"
			  | prt (SOME (x : Ast.ty)) = "\t\tType: " ^ PrettyPrint.ppty x ^ "\n"

			fun pra NONE = "\t\t AST: NONE\n"
			  | pra (SOME (x : Ast.exp)) = "\t\t AST: " ^ PrettyPrint.ppexp x ^ "\n"

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
			val {venv,tenv} = !scope
			val _ = print "* Value Environment:\n"
			val _ = print_env (!venv) 
			val _ = print "* Type Environment:\n"
			val _ = print_env (!tenv)
		in () end

end
