structure ML2PP0Tests =
struct
	fun run_all_tests () = let
		val _ =
		 (ParseTests.run_all_tests ();
		 OptimiserTests.run_all_tests ();
		 CodeGenTests.run_all_tests ())
		val _ = print ("\nTotal: " ^ Int.toString (!Test.totalCount) ^ "\nFailures: " ^ Int.toString (!Test.failedCount) ^ "\n")
		in
			if (!Test.failedCount) > 0 then raise (Fail (Int.toString (!Test.failedCount) ^ " tests failed")) else ()
		end
end
