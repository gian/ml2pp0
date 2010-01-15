structure Ast =
struct
	type symbol = Symbol.symbol
	type 'a table = 'a Symbol.table

	datatype fixity = 
			Infix of int option
		  | Infixr of int option
		  | Nonfix

	datatype dec = 
			ExpDec of ast 
		  | NullDec
		  | LocalDec 
		  | ValDec of {tyvars: ty list,valBind : bind list,recBind : bind list}
		  | FunDec of ty list * (clause list list)
		  | TypeDec of bind list
		  | KindDec of bind list
		  | DatatypeDec of bind list
		  | AbstypeDec
	      | ExceptionDec 
		  | OpenDec 
		  | FixDec of fixity * symbol list * (ty option * ast option) symtab ref
		 and ast = Node of ast_node * ty option * ((ty option * ast option) symtab ref) * ast list 
	     and ast_node =
			Handle	(* [ exp, matches ] *)
		  | Match (* [pat,exp] *) 
		  | App (* [tm1, tm2] *)
		  | Constraint of ty (* [exp] *)
		  | Fn (* [matches] *)
		  | Case (* [exp, matches] *)
		  | While (* [cond, exp] *)
		  | If (* cond, tbr, fbr *)
		  | Raise (* [exp] *)
		  | Op of symbol
		  | Var of symbol
		  | Selector (* exp *)
		  | Record (* interleaved [t1,t2,t3,t4] = {t1=t2,t3=t4} *)
		  | Unit
		  | Seq (* [exps] *)
		  | Tuple (* exps *)
		  | Vector (* exps *)
		  | List (* exps *)
		  | Let of dec list (* [exp] *)
		  | Int of int
		  | Word of word
		  | Real of real
		  | String of string
		  | Char of char
		  | Bool of bool
		  | BuiltIn of string * ty
		  | AsPat (* exp, exp *)
		  | ConstraintPat of ty (* exp *) 
		  | AppPat (* exps *)
		  | VarPat of symbol 
		  | OpPat of symbol
		  | ConstPat (* exp *)
		  | WildPat
		  | TuplePat (* exps *)
		  | ListPat (* exps *)
		  | UnitPat
		  | RecordPat of bool (* flexible, [pats] *)
		  | FieldPat (* Fields, interleaved *)
		 and bind =
			ValBind of ast * ast 
		  | ValRecBind of ast * (ast list)
		  | TypeBind of {def : ty, tycon : ty, tyvars : ty list}
		  | DatatypeReplBind of ty * ty
		  | DatatypeBind of 
		     {cons: (ast * ty option) list, tycon: ty, tyvars: ty list}
		 and ty =
			TupleTy of ty list
		  | ArrowTy of ty * ty
		  | VarTy of symbol 
		  | RecordTy of (ast * ty) list
		  | UnitTy
		  | TyConTy of ty * ty list
		  | StrTy of symbol list
		  | ListTy of ty
		  | IntTy
		  | StringTy
		  | BoolTy
		  | RealTy
		  | CharTy
		  | WordTy
		  | VectorTy of ty * ast
		  | UVar of int
		  | PolyTy of int
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

		 withtype clause = {pats : ast list,
    	           resultType : ty option,
        	       body : ast}
			  and 'a symtab = {venv : 'a Symbol.table ref,
				            tenv : 'a Symbol.table ref,
							iter_order : Symbol.symbol list ref}


	type symbol_data = ty option * ast option

	type program = dec list
end
