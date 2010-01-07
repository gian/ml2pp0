structure Lml =
struct
 fun initialise () =
  	let
    (*		val _ = Optimiser.addPass ("nullOpt", fn x => x) *)
	(*	val _ = Optimiser.addPass ("constFold", ConstFold.optConstFold) *)
	in
		()
	end
(*
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
	    val ast = Parse.parse' smlfile
		val ast' = Syntax.runAllPasses ast
		val _ = Symtab.print_scope (Symtab.top_level)
		val _ = print "AST DUMP:\n"
		val _ = print (PrettyPrint.prettyPrint ast')
		val _ = print "\nElaborate:\n"
		val _ = Elaborate.constr ast'
		val _ = Elaborate.print_constr (!Elaborate.venv) 
		val _ = print "\n"
		val ast2 = Optimiser.runAllPasses ast 
		val l = Intermediate.translate ast'
		val _ = print "CODE DUMP:\n"
		val _ = print (Intermediate.emit l [] [])
	in
		()
	end

end

structure Main =
struct
	fun main () = 
		let 
			val _ = Lml.initialise ()
			val args = CommandLine.arguments ()
		in (Lml.lml (hd args);()) end
end

val _ = Main.main ()

