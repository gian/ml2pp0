structure Ast =
struct
	type symbol = Symbol.symbol
	type 'a table = 'a Symbol.table

	datatype fixity = 
			Infix of int option
		  | Infixr of int option
		  | Nonfix

	datatype dec = 
			ExpDec of {attr : attr list, exp : exp}
		  | NullDec
		  | LocalDec of {attr: attr list,dec1: dec list,dec2 :dec list, symtab : (ty option * exp option) symtab ref}
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
			 body : dec list}
	      | ExceptionDec of {attr : attr list}
		  | OpenDec of {attr : attr list} 
		  | FixDec of {attr : attr list, fixity: fixity,ops:symbol list, symtab : (ty option * exp option) symtab ref}
	     and exp =
			Handle of 
				{attr : attr list, exp : exp, match : (pat * exp) list}
		  | App of {attr : attr list, exps : exp list}
		  | BinOp of {attr : attr list, opr : opr, lhs: exp, rhs: exp}
		  | Constraint of {attr : attr list, exp : exp, ty : ty}
		  | Fn of {attr : attr list, match : (pat * exp) list, symtab : (ty option * exp option) symtab ref}
		  | Case of {attr: attr list, exp: exp, match: (pat * exp) list}
		  | While of {attr: attr list, test : exp, exp : exp}
		  | If of {attr:attr list, cond: exp, tbr: exp, fbr: exp}
		  | Raise of {attr:attr list, exp : exp}
		  | Op of {attr: attr list, symbol : symbol, symtab : (ty option * exp option) symtab ref}
		  | Var of {attr: attr list, name : symbol, symtab : (ty option * exp option) symtab ref}
		  | Selector of {attr: attr list, exp : exp}
		  | Record of {attr: attr list, fields : (exp * exp) list}
		  | Unit
		  | Seq of {attr: attr list, exps : exp list}
		  | Tuple of {attr: attr list, exps : exp list}
		  | List of {attr: attr list, exps : exp list}
		  | Let of {attr: attr list, decs : dec list, exp : exp, symtab : (ty option * exp option) symtab ref}
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
		  | VarPat of {attr: attr list, name : symbol, symtab : (ty option * exp option) symtab ref}
		  | OpPat of {attr: attr list, symbol : symbol, symtab : (ty option * exp option) symtab ref}
		  | ConstPat of exp
		  | WildPat
		  | TuplePat of pat list
		  | ListPat of pat list
		  | UnitPat
		  | RecordPat of {flexible : bool, pats : pat list}
		  | FieldPat of exp * pat
		 and bind =
			ValBind of pat * exp
		  | ValRecBind of pat * ((pat * exp) list)
		  | TypeBind of {def : ty, tycon : ty, tyvars : ty list}
		  | DatatypeReplBind of {lhs : ty, rhs : ty}
		  | DatatypeBind of 
		     {cons: (exp * ty option) list, tycon: ty, tyvars: ty list}
		 and ty =
			TupleTy of ty list
		  | ArrowTy of ty * ty
		  | VarTy of symbol * ((ty option * exp option) symtab ref)
		  | RecordTy of (exp * ty) list
		  | UnitTy
		  | TyConTy of ty * ty list
		  | StrTy of symbol list
		  | UVar of int
		  | PolyTy of int
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
		  | SOpr of symbol
		  | Plus
		  | Minus
		  | Times
		  | Div
		  | RDiv
		  | StrConcat
		  | Cons
		  | Concat
		  | Mod
		  | Equal
		  | NEqual
		  | LT
		  | GT
		  | LTEqual
		  | GTEqual
		  | Assign
		  | Compose
		  | Before

		 withtype clause = {pats : pat list,
    	           resultType : ty option,
        	       body : exp}
			  and 'a symtab = {venv : 'a Symbol.table ref,
				            tenv : 'a Symbol.table ref}


	type symbol_data = ty option * exp option

	type match = (pat * exp) list

	type program = dec list
end
