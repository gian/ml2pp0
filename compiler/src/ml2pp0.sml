structure Lml =
struct
 fun initialise () =
  	let
		val _ = Optimiser.addPass ("nullOpt", fn x => ())
		val _ = Optimiser.addPass ("constFold", ConstFold.optConstFold) 
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
	
		val _ = print "AST DUMP:\n"
		val _ = print (PrettyPrint.prettyPrint ast)

		val ast' = Syntax.runAllPasses ast

		val _ = print "SCOPE DUMP:\n"
		val _ = Symtab.print_scope (Symtab.top_level)

		val _ = print "\nElaborate:\n"
		val _ = Elaborate.constr (Symtab.top_level)
		val _ = Elaborate.print_constr (!Elaborate.venv) 
		val _ = print "\n"

		val _ = print "SCOPE DUMP CONSTRAINED:\n"
		val _ = Symtab.print_scope (Symtab.top_level)

		val _ = Optimiser.runAllPasses Symtab.top_level
		val _ = print "SCOPE DUMP (post-Optimiser):\n"
		val _ = Symtab.print_scope (Symtab.top_level)
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

