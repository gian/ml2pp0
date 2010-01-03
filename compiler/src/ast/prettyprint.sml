structure PrettyPrint =
struct
	open Ast
	structure S = Symbol

	fun ppdec (ExpDec {exp=exp,...}) = ppexp exp
	  | ppdec NullDec = "<NULLDEC>"
	  | ppdec (LocalDec {dec1=dec1,dec2=dec2,...}) =
	  	"local\n" ^ ppdecs dec1 ^ "\nin\n" ^ ppdecs dec2 ^ "\nend\n"
	  | ppdec (ValDec {tyvars=tyvars,valBind=valBind,recBind=recBind,...}) =
	  		"val " ^ ppbinds valBind ^ ppbinds recBind
	  | ppdec (FunDec {tyvars=tyvars,clauses=clauses,...}) = 
	  		"fun " ^ ppclauses2 clauses
	  | ppdec (TypeDec {tyBind=tyBind,...}) =
	  		"type " ^ ppbinds tyBind
	  | ppdec (FixDec {fixity,ops,...}) = ppfixity fixity ^ " " ^
	  		(String.concatWith " " (map S.toString ops))
	  | ppdec _ = "<unpretty-printed dec>"
	and ppexp (Handle {exp,match,...}) = "(" ^ppexp exp^ ") handle ..."
	  | ppexp (App {exps=[],...}) = ""
	  | ppexp (App {exps=[h],attr=a}) = ppexp h
	  | ppexp (App {exps=h::t,attr=a}) = 
	  		ppexp h ^ " (" ^ ppexp (App {exps=t,attr=a}) ^ ")"
	  | ppexp (BinOp {opr=opr,lhs,rhs,...}) = 
	  		ppopr opr ^ " (" ^ ppexp lhs ^ ", " ^ ppexp rhs ^ ")"
	  | ppexp (Constraint {exp=exp,ty=ty,...}) =
			ppexp exp ^ " : " ^ ppty ty
	  | ppexp (Fn {match,...}) = "fn " ^ ppmatch match
	  | ppexp (Case x) = "<case>"
	  | ppexp (While x) = "<while>"
	  | ppexp (If {cond,tbr,fbr,...}) = 
	  	"if " ^ ppexp cond ^ " then " ^ ppexp tbr ^ " else " ^ ppexp fbr
	  | ppexp (Op {symbol,...}) = "op " ^ S.toString symbol
	  | ppexp (Var {name,...}) = S.toString name
	  | ppexp (Selector {exp,...}) = "#" ^ ppexp exp
	  | ppexp Unit = "()"
	  | ppexp (Seq {exps,...}) = 
	  		"(" ^ String.concatWith "; " (map ppexp exps) ^ ")"
	  | ppexp (Int i) = Int.toString i
	  | ppexp (Word w) = Word32.toString w
	  | ppexp (Real r) = Real.toString r
	  | ppexp (String s) = "\"" ^ s ^ "\""
	  | ppexp (Char c) = "#\"" ^ String.str c ^ "\""
	  | ppexp (Bool b) = if b then "true" else "false"
	  | ppexp (Let {decs,exp,...}) = 
	  	"\nlet\n" ^ ppdecs decs ^ "in\n   " ^ ppexp exp ^ "\nend"
	  | ppexp _ = "<unpretty-printed exp>"
	and ppbinds [] = ""
	  | ppbinds [h] = ppbind h
	  | ppbinds (h::t) = ppbind h ^ "\n" ^ ppbinds t
	and ppbind (ValBind (p,e)) = pppat p ^ " = " ^ ppexp e
	  | ppbind (ValRecBind (p,_)) = " rec " ^ pppat p ^ " = ..."
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
		String.concatWith " " (map pppat pats) ^ " = " ^ ppexp body
	  | ppclause {pats,resultType=SOME x,body} =
	    String.concatWith " " (map pppat pats) ^ 
			" : " ^ ppty x ^
			" = " ^ ppexp body
	and ppty (TupleTy t) = String.concatWith " * " (map ppty t)
	  | ppty (ArrowTy (t,t')) = ppty t ^ " -> " ^ ppty t'
	  | ppty (VarTy s) = S.toString s
	  | ppty (RecordTy l) = 
	  	"{" ^ (String.concatWith ", " 
			(map (fn (x,y) => ppexp x ^ " : " ^ ppty y) l)) ^ "}"
	  | ppty UnitTy = "unit"
	  | ppty (TyConTy (t,[])) = ppty t
	  | ppty (TyConTy (t,t')) = 
	  	"(" ^ (String.concatWith "," (map ppty t')) ^ ") " ^ ppty t
	  | ppty _ = "<unpretty-printed ty>"
	and ppopr BOr = "orelse"
	  | ppopr BAnd = "andalso"
	  | ppopr Plus = "+"
	  | ppopr Minus = "-"
	  | ppopr Times = "*"
	  | ppopr Div = "div"
	  | ppopr RDiv = "/"
	  | ppopr StrConcat = "^"
	  | ppopr Cons = "::"
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
	  | ppopr (SOpr s) = S.toString s
	and ppmatch l =
		String.concatWith "\n  | " (
			map (fn (p,e) => pppat p ^ " => " ^ ppexp e) l
		)
	and pppat (AsPat (p1,p2)) = pppat p1 ^ " as " ^ pppat p2
	  | pppat (ConstraintPat (p,t)) = pppat p ^ " : " ^ ppty t
	  | pppat (AppPat []) = ""
	  | pppat (AppPat [h]) = pppat h
	  | pppat (AppPat (h::t)) = pppat h ^ " (" ^ pppat (AppPat t) ^ ")"
	  | pppat (VarPat {name,...}) = S.toString name
	  | pppat (OpPat {symbol,...}) = "op " ^ S.toString symbol
	  | pppat (ConstPat e) = ppexp e
	  | pppat (WildPat) = "_"
	  | pppat (TuplePat p) = 
	  	"(" ^ (String.concatWith ", " (map pppat p)) ^ ")"
	  | pppat (ListPat l) = 
	  	"[" ^ (String.concatWith ", " (map pppat l)) ^ "]"
	  | pppat (UnitPat) = "()"
	  | pppat (RecordPat {flexible=true, pats}) =
	  	"{" ^ (String.concatWith ", " (map pppat pats)) ^ ", ...}"
	  | pppat (FieldPat (e,p)) = ppexp e ^ "=" ^ pppat p
	and ppfixity (Infix (SOME x)) = "infix " ^ Int.toString x ^ " "
	  | ppfixity (Infix NONE) = "infix "
	  | ppfixity (Infixr (SOME x)) = "infixr " ^ Int.toString x ^ " "
	  | ppfixity (Infixr NONE) = "infixr "
	  | ppfixity (Nonfix) = "nonfix "

	fun prettyPrint p = ppdecs p

end

