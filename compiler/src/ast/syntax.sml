structure Syntax =
struct
	structure S = Symbol

	val passes = [
		("SyntaxOperatorUnflatten", 
			SyntaxOperatorUnflatten.translate ()),
		("SyntaxSingleApp",
			SyntaxSingleApp.translate ()),
		("SyntaxPopulateSymtabs",
			SyntaxPopulateSymtabs.translate ()),
		("SyntaxFundecAnon",
			SyntaxFundecAnon.translate ()),
		("SyntaxClosureConv",
			SyntaxClosureConv.translate ()),
		("SyntaxDefunctionalise",
			SyntaxDefunctionalise.translate ()),
		("SyntaxCollapseDecs",
			SyntaxCollapseDecs.translate ())
	]

	fun runAllPasses prog =
	  ( print "[Syntax translation passes]\n";
		foldl (fn ((name,pass),prog') => 
			(print (" * [" ^ name ^ "]\n");
			 pass prog')) prog passes)

end

