structure CodeGenTests =
struct
	open Test
	open CodeGen

	val tests = [
	fn () => (* valid_code *)
	let
			val p = Parse.parse "tests/sources/codegen.sml"
	in
		assert ("valid_code", false)
	end
	]

	fun run_all_tests () = (print "[CodeGenTests]\n"; app run_test tests) 
end
