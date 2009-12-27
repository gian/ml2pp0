signature OPTIMISER =
sig
	type typed
	type 'a ast

	type optimiser_pass
	
	val addPass : optimiser_pass -> unit
	val removePass : string -> unit
	val runPass : optimiser_pass * typed ast list -> typed ast list
	val runAllPasses : typed ast list -> typed ast list
end