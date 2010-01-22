structure Dependent =
struct
	structure A = Ast

	fun equal (x,y) = 
	  	let
			val _ = print ("DEPENDENT: " ^ PrettyPrint.ppexp x ^ " < " ^ PrettyPrint.ppexp y ^ "\n")
		in
			true
		end

end
