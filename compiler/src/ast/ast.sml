structure AST =
struct

	type fixity = int

	datatype dec = 
			ExpDec of {attr : attr list, exp : exp}
		  | NullDec
		  | LocalDec of {attr: attr list,dec1: dec list,dec2 :dec list}
		  | ValDec of 
		  	{attr:attr list,
			 tyvars: ty list,
			 valBind : bind list,
			 recBind : bind list}
		  | FunDec of
		  	{attr:attr list,
			 tyvars : ty list,
			 clauses : clause list list}
		  | TypeDec of
		  	{attr:attr list,
			 tyBind : bind}
		  | DatatypeDec of
		    {attr:attr list,
			 tyBind : bind}
		  | AbstypeDec of
		    {attr:attr list,
			 tyBind : bind,
			 body : dec list list}
	      | ExceptionDec of {attr : attr list}
		  | OpenDec of {attr : attr list} 
		  | FixDec of {attr : attr list, fixity : fixity,ops=symbol list}
	     and exp =

		 and pat =

		 and bind =

		 and ty =
	
		 and attr =
		 	Left of int
		  | Right of int
		  | Type of ty
		  | Commutative
		  | Associative
		  | Info of string

	type clause = {pats : A.pat list,
    	           resultType : A.ty option,
        	       body : A.exp}

	type program = dec list list

end
