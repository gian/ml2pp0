structure Lml =
struct
 (* fun initialise () =
  	let
		val _ = Optimiser.addPass ("nullOpt", fn x => x)
		val _ = Optimiser.addPass ("constFold", ConstFold.optConstFold)
	in
		()
	end

  fun lml "-tests" = ML2PP0Tests.run_all_tests() 
   | lml (smlfile) = 
    let 
	    val (ast,c) = Types.stype (Parse.parse smlfile)
		val ast' = Optimiser.runAllPasses ast
		val _ = print (TypedAST.pptypedast ast')
	in
		()
	end *)

	fun lml (smlfile) = 
    let 
	    val ast = (Syntax.unflatten_ops (Parse.parse' smlfile))
		val _ = print (PrettyPrint.prettyPrint ast)
		val _ = print "\n"
		val l = map Intermediate.translate ast
		val _ = app (fn (p,i) => print (Intermediate.emit i)) l
	in
		()
	end

end

structure Main =
struct
	fun main () = 
		let 
			(*val _ = Lml.initialise ()*)
			val args = CommandLine.arguments ()
		in (Lml.lml (hd args);()) end
end

val _ = Main.main ()

