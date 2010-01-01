structure Ast =
struct
	type symbol = Symbol.symbol

	datatype fixity = 
			Infix of int option
		  | Infixr of int option
		  | Nonfix

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
			 tyBind : bind list}
		  | DatatypeDec of
		    {attr:attr list,
			 tyBind : bind list}
		  | AbstypeDec of
		    {attr:attr list,
			 tyBind : bind list,
			 body : dec list list}
	      | ExceptionDec of {attr : attr list}
		  | OpenDec of {attr : attr list} 
		  | FixDec of {attr : attr list, fixity: fixity,ops:symbol list}
	     and exp =
			Handle of 
				{attr : attr list, exp : exp, match : (pat * exp) list}
		  | BinOp of {attr : attr list, opr : opr, lhs: exp, rhs: exp}
		  | Constraint of {attr : attr list, exp : exp, ty : ty}
		  | Fn of {attr : attr list, match : (pat * exp) list}
		  | Case of {attr: attr list, exp: exp, match: (pat * exp) list}
		  | While of {attr: attr list, test : exp, exp : exp}
		  | If of {attr:attr list, cond: exp, tbr: exp, fbr: exp}
		  | Raise of {attr:attr list, exp : exp}
		  | Op of {attr: attr list, symbol : symbol}
		  | Var of {attr: attr list, name : symbol}
		  | Selector of {attr: attr list, exp : exp}
		  | Record of {attr: attr list, fields : (exp * exp) list}
		  | Unit of {attr: attr list}
		  | Seq of {attr: attr list, exps : exp list}
		  | Tuple of {attr: attr list, exps : exp list}
		  | List of {attr: attr list, exps : exp list}
		  | Let of {attr: attr list, decs : dec list, exp : exp}
		  | Int of int
		  | Word of word
		  | Real of real
		  | String of string
		  | Char of char
		  | Bool of bool
		 and pat =
			AsPat of pat * pat
		  | ConstraintPat of pat * ty
		  | AppPat of pat list
		  | VarPat of {attr: attr list, name : symbol}
		  | OpPat of {attr: attr list, symbol : symbol}
		  | ConstPat of exp
		  | WildPat
		  | TuplePat of pat list
		  | ListPat of pat list
		  | UnitPat
		  | RecordPat of {flexible : bool, pats : pat list}
		  | FieldPat of exp * pat
		 and bind =
			ValBind of pat * exp
		  | ValRecBind of pat * (pat * exp) list
		  | TypeBind of {def : ty, tycon : ty, tyvars : ty list}
		  | DatatypeReplBind of {lhs : ty, rhs : ty}
		  | DatatypeBind of 
		     {cons: (exp * ty option) list, tycon: ty, tyvars: ty list}
		 and ty =
			TupleTy of ty list
		  | ArrowTy of ty * ty
		  | VarTy of symbol
		  | RecordTy of (exp * ty) list
		  | UnitTy
		  | TyConTy of symbol * ty list
		 and attr =
		 	Left of int
		  | Right of int
		  | Type of ty
		  | Commutative
		  | Associative
		  | Info of string
		 and opr =
		 	BOr
		  | BAnd
		 withtype clause = {pats : pat list,
    	           resultType : ty option,
        	       body : exp}
	
	type match = (pat * exp) list

	type program = dec list list

end
