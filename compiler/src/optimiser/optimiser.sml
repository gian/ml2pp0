structure Optimiser =
struct
    type dec = Ast.dec

    type optimiser_pass =
		string * (Symtab.symbol_data Symtab.symtab ref -> unit)
  
	val passes = ref [] : optimiser_pass list ref

    fun addPass pass = passes := (!passes) @ [pass] 
    fun removePass name = passes := (List.filter (fn (x,_) => x <> name) (!passes))
    fun runPass symtab (name,f) = 
		let
			val _ = print ("[optimiser: applying " ^ name ^ "]\n")
		in
			f symtab
		end

    fun runAllPasses symtab = List.app (runPass symtab) (!passes) 
end
(* vim: ts=4 
*)
