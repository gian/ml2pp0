structure OptimiserTests =
struct
	open Test
	open Optimiser

	val tests = [
	fn () => (* optConstFold *)
	let
	in
		assert ("optConstFold", false)
	end
	]

	fun run_all_tests () = (print "[OptimiserTests]\n"; app run_test tests) 
end
