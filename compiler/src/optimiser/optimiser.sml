structure Optimiser : OPTIMISER =
struct
    type typed = TypedAST.typed
    type 'a ast = 'a TypedAST.ast

    type optimiser_pass = string * (typed ast -> typed ast)
  
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