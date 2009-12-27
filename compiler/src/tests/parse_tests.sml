structure ParseTests =
struct
	open Test
	open Parse

	val tests = [
	fn () => (* ground_lit *)
	let
	in
		assert ("ground_lit_int", false) ;
		assert ("ground_lit_string", false) ;
		assert ("ground_lit_bool", false) ;
		assert ("ground_lit_real", false) 
	end
	]

	fun run_all_tests () = (print "[ParseTests]\n"; app run_test tests) 
end
