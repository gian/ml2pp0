structure PrettyPrint =
struct
	open Ast
	structure S = Symbol

	fun ppdec (ExpDec exp) = ppexp exp
	  | ppdec NullDec = "<NULLDEC>"
	  | ppdec (LocalDec) = "local ... in ... end"
	  | ppdec (ValDec {tyvars=tyvars,valBind=valBind,recBind=recBind,...}) =
	  		"val " ^ ppbinds valBind ^ ppbinds recBind
	  | ppdec (FunDec (tyvars,clauses)) = 
	  		"fun " ^ ppclauses2 clauses
	  | ppdec (TypeDec tyBind) =
	  		"type " ^ ppbinds tyBind
	  | ppdec (KindDec tyBind) =
	  		"kind " ^ ppbinds tyBind
	  | ppdec (FixDec (fixity,ops,st)) = ppfixity fixity ^ " " ^
	  		(String.concatWith " " (map S.toString ops))
	  | ppdec _ = "<unpretty-printed dec>"
	and ppexp (Node (nd, NONE, symtab, [])) = ppast nd
	  | ppexp (Node (nd, SOME x, symtab, [])) = ppast nd ^ " : " ^ ppty x
	  | ppexp (Node (nd, NONE, symtab, ch)) = ppast nd ^ " [" ^ (String.concatWith ", " (map ppexp ch)) ^ "]"
	  | ppexp (Node (nd, SOME x, symtab, ch)) = ppexp (Node (nd, NONE, symtab, ch)) ^ " : " ^ ppty x
	and ppast Match = "Match"
	  | ppast App = "App"
	  | ppast (Constraint t) = "Constraint(" ^ ppty t ^ ")"
	  | ppast Fn = "Fn"
	  | ppast Case = "Case"
	  | ppast While = "While"
	  | ppast If = "If"
	  | ppast Raise = "Raise"
	  | ppast (Op s) = "op " ^ S.toString s
	  | ppast (Var s) = S.toString s
	  | ppast Selector = "Selector"
	  | ppast Record = "Record"
	  | ppast Unit = "()"
	  | ppast Seq = "Seq"
	  | ppast Tuple = "Tuple"
	  | ppast Vector = "Vector"
	  | ppast List = "List"
	  | ppast (Let d) = "Let"
	  | ppast (Int i) = Int.toString i
	  | ppast (Word w) = Word32.toString w
	  | ppast (Real r) = Real.toString r
	  | ppast (String s) = "\"" ^ String.toCString s ^ "\""
	  | ppast (Char c) = "#\"" ^ String.str c ^ "\""
	  | ppast (Bool b) = if b then "true" else "false"
	  | ppast (BuiltIn (s,t)) = "<builtin " ^ s ^ " : " ^ ppty t ^ ">"
	  | ppast AsPat = "AsPat"
	  | ppast (ConstraintPat t) = "ConstraintPat(" ^ ppty t ^ ")"
	  | ppast AppPat = "AppPat"
	  | ppast (VarPat s) = "VarPat(" ^ S.toString s ^ ")"
	  | ppast (OpPat s) = "OpPat("  ^ S.toString s ^ ")"
	  | ppast TuplePat = "TuplePat"
	  | ppast ListPat = "ListPat"
	  | ppast UnitPat = "UnitPat"
	  | ppast ConstPat = "ConstPat"
	  | ppast (RecordPat true) = "RecordPat(...)"
	  | ppast (RecordPat false) = "RecordPat"
	  | ppast FieldPat = "FieldPat"
	  | ppast WildPat = "_"
	  | ppast _ = raise Fail "ppast: unmatched"
	and ppbinds [] = ""
	  | ppbinds [h] = ppbind h
	  | ppbinds (h::t) = ppbind h ^ " \nand " ^ ppbinds t
	and ppbind (ValBind (p,e)) = ppexp p ^ " = " ^ ppexp e
	  | ppbind (ValRecBind (p,b)) = "rec " ^ ppexp p ^ " = fn " ^ 
	  		(String.concatWith "\n\t| " (map ppexp b))
	  | ppbind (TypeBind {def,tycon,tyvars}) = 
	  	let
			val tv = if length tyvars = 0 then "" else 
				"(" ^ (String.concatWith "," (map ppty tyvars)) ^ ") "
			val tc = ppty tycon
			val d = ppty def
		in
			tv ^ tc ^ " = " ^ d
		end
	  | ppbind _ = "<unpretty-printed bind>"
	and ppdecs [] = ""
	  | ppdecs (h::t) = ppdec h ^ ";\n" ^ ppdecs t
	and ppclauses2 l = String.concatWith "\nand " (map ppclauses l)
	and ppclauses l = String.concatWith "\n  | " (map ppclause l)
	and ppclause {pats,resultType=NONE,body} =
		String.concatWith " " (map ppexp pats) ^ " = " ^ ppexp body
	  | ppclause {pats,resultType=SOME x,body} =
	    String.concatWith " " (map ppexp pats) ^ 
			" : " ^ ppty x ^
			" = " ^ ppexp body
	and ppty (TupleTy t) = String.concatWith " * " (map ppty t)
	  | ppty (ArrowTy (t,t')) = ppty t ^ " -> " ^ ppty t'
	  | ppty (VarTy s) = S.toString s
	  | ppty (RecordTy l) = 
	  	"{" ^ (String.concatWith ", " 
			(map (fn (x,y) => ppexp x ^ " : " ^ ppty y) l)) ^ "}"
	  | ppty UnitTy = "_unit"
	  | ppty (TyConTy (t,[])) = ppty t
	  | ppty (TyConTy (t,t')) = 
	  	"(" ^ (String.concatWith "," (map ppty t')) ^ ") " ^ ppty t
	  | ppty (ListTy t) = ppty t ^ " list"
	  | ppty (UVar i) = "?X" ^ Int.toString i
	  | ppty (PolyTy i) = "'" ^ String.str 
	  							(Char.chr (Char.ord #"a" + i))
	  | ppty IntTy = "int"
	  | ppty StringTy = "string"
	  | ppty BoolTy = "bool"
	  | ppty RealTy = "real"
	  | ppty CharTy = "char"
	  | ppty WordTy = "word"
	  | ppty (DepTy (t,e)) = ppty t ^ "!" ^ ppexp' e
	  | ppty (VectorTy t) = ppty t ^ " vector"
	  | ppty _ = "<unpretty-printed ty>"
	and ppexp' (Node (Int i, _, _, _)) = Int.toString i
	  | ppexp' (Node (Var i, _, _, _)) = Symbol.toString i
	  | ppexp' (Node (App,_,_,[t1,t2])) = ppexp' t1 ^ ppexp' t2
	  | ppexp' (Node (Tuple,_,_,ch)) = "(" ^ String.concatWith "," (
	  										map ppexp' ch) ^ ")"
	  | ppexp' e = raise Fail ("Invalid dependent type term: " ^ ppexp e)
	and ppopr BOr = "orelse"
	  | ppopr BAnd = "andalso"
	  | ppopr Plus = "+"
	  | ppopr Minus = "-"
	  | ppopr Times = "*"
	  | ppopr Div = "div"
	  | ppopr RDiv = "/"
	  | ppopr StrConcat = "^"
	  | ppopr Cons = "::"
	  | ppopr Concat = "@"
	  | ppopr Mod = "mod"
	  | ppopr Equal = "="
	  | ppopr NEqual = "<>"
	  | ppopr LT = "<"
	  | ppopr GT = ">"
	  | ppopr LTEqual = "<="
	  | ppopr GTEqual = ">="
	  | ppopr Assign = ":="
	  | ppopr Compose = "o"
	  | ppopr Before = "before"
	  | ppopr (SOpr s) = "Sopr("^(S.toString s)^")"
	and ppmatch l =
		String.concatWith "\n  | " (
			map (fn (p,e) => ppexp p ^ " => " ^ ppexp e) l
		)
	and ppfixity (Infix (SOME x)) = "infix " ^ Int.toString x ^ " "
	  | ppfixity (Infix NONE) = "infix "
	  | ppfixity (Infixr (SOME x)) = "infixr " ^ Int.toString x ^ " "
	  | ppfixity (Infixr NONE) = "infixr "
	  | ppfixity (Nonfix) = "nonfix "

	fun prettyPrint p = ppdecs p

end

