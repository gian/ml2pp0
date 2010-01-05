structure Optimiser =
struct
    type dec = Ast.dec

    type optimiser_pass = string * (dec list -> dec list)
  
	val passes = ref [] : optimiser_pass list ref

    fun addPass pass = passes := (!passes) @ [pass] 
    fun removePass name = passes := (List.filter (fn (x,_) => x <> name) (!passes))
    fun runPass ((name,f), inp) = 
		let
			val _ = print ("[optimiser: applying " ^ name ^ "]\n")
		in
			f inp
		end

    fun runAllPasses ast = List.foldl runPass ast (!passes) 
end
(* vim: ts=4 
*)
