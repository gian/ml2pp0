structure Dependent =
struct
	structure A = Ast

	fun equal (A.Node (A.Int i, _, _, _), A.Node (A.Int j, _, _, _)) =
		i = j
	  | equal _ = false

end
