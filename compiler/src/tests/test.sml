structure Test =
struct
	exception TestFailed of string

	val totalCount = ref 0
	val failedCount = ref 0

	fun pad s n =
		if size s >= n then s else pad (" " ^ s) n

	fun assert (str, true) = (totalCount := !totalCount + 1; print ("[TEST] " ^ pad str 24 ^ ":\tpassed\n"))
	  | assert (str, false) = (totalCount := !totalCount + 1; failedCount := !failedCount + 1; raise (TestFailed str))

	fun assertFalse (s, v) = assert (s, not v)

	fun run_test f = f () handle TestFailed m =>
		print ("[TEST] " ^ pad m 24 ^ ":\tFAILED\n")
		                       | e => (print ("[TEST] " ^ pad "Exception during test" 17 ^ "\n"); raise e)
end
