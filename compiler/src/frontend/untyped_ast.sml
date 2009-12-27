(* Untyped abstract syntax tree *)
structure Absyn =
struct


   datatype behavty =
      BTChoice of behavty * behavty
   |  BTIdentifier of string * ty option
   |  BTCompose of behavty * behavty
   |  BTSend of behavty * ty option
   |  BTRecv of behavty * ty option
   |  BTSeq of behavty * behavty
   |  BTStar of behavty
   |  BTUnapplied of behavty
   |  BTFinal
   |  BTSkip
   and ty =
       TyCon of ty * ty
     | TyVar of int
     | TyName of string
     | TyPoly of string
     | TyArrow of ty * ty
     | TyTup of ty * ty
     | TyNil
     | LVar of string
   type identifier = string * ty option

   datatype opr =
      Plus
   |  Minus
   |  Times
   |  Divide
   |  Eq
   |  LtEq
   |  GtEq
   |  Lt
   |  Gt
   |  NEq
   |  Assign
   |  Cons

   datatype expr =
      Integer of int
   |  String of string
   |  AnonFn of (expr * expr) list
   |  Nil
   |  Unit
   |  Var of identifier
   |  Deref of expr
   |  UMinus of expr
   |  BinOp of expr * opr * expr
   |  BNot of expr
   |  If of expr * expr * expr
   |  Let of string * expr * expr
   |  Seq of expr * expr
   |  TypeAnnotation of expr * ty
   |  Tuple of expr list
   |  List of expr list
   |  App of expr * expr
   |  True
   |  False
   and stm =
      ValBinding of identifier * expr
   |  TyBinding of string * ty
   |  DatatypeBinding of string * (string * ty option) list
   |  StructBinding of string * stm list
   |  SigBinding of string * stm list 

   (* Pretty Debug.print_dbg code follows *)

 val newType = ref 0
 
 fun mkTy NONE = (newType := !newType + 1; "?X" ^ Int.toString (!newType))
   | mkTy (SOME x) = ppty x
 and ppbehavty (BTChoice(b1,b2)) = "(" ^ ppbehavty b1 ^ " # " ^ (ppbehavty b2) ^ ")"
   | ppbehavty (BTIdentifier(s,t)) = s
   | ppbehavty (BTCompose(b1,b2)) = "(" ^ ppbehavty b1 ^ " || " ^ (ppbehavty b2) ^ ")"
   | ppbehavty (BTSend(b,t)) = mkTy t
   | ppbehavty (BTRecv(b,t)) = mkTy t
   | ppbehavty (BTSeq(b1,b2)) = "(" ^ ppbehavty b1 ^ ");(" ^ ppbehavty b2 ^ ")"
   | ppbehavty (BTStar b) = "(" ^ ppbehavty b ^ ")*"
   | ppbehavty (BTUnapplied b) = " % "
   | ppbehavty (BTSkip) = "SKIP" 
   | ppbehavty (BTFinal) = "END"
   and ppty (TyName s) = s
   | ppty (TyCon(t1,t2)) = ppty t1 ^ " " ^ ppty t2
   | ppty (TyArrow(TyArrow(t1',t2'),t2)) = "(" ^ ppty (TyArrow(t1',t2')) ^ ") -> " ^ ppty t2
   | ppty (TyArrow(t1,t2)) = ppty t1 ^ " -> " ^ ppty t2
   | ppty (TyVar n) = "?X" ^ Int.toString n
   | ppty (LVar s) = s
   | ppty (TyPoly s) = s
   | ppty (TyNil) = "nil list"
   
   fun ppopr Plus = "+"
   | ppopr Minus = "-"
   | ppopr Times = "*"
   | ppopr Divide = "/"
   | ppopr Eq = "="
   | ppopr LtEq = "<="
   | ppopr GtEq = ">="
   | ppopr Lt = "<"
   | ppopr Gt = ">"
   | ppopr NEq = "<>"
   | ppopr Assign = ":="
   | ppopr Cons = "::"

   fun ppexpr (Integer i) = Int.toString i
   | ppexpr ( String s ) = s
   | ppexpr ( AnonFn l ) = "fn ... = ..."
   | ppexpr ( Nil ) = "nil"
   | ppexpr ( Unit ) = "()"
   | ppexpr ( Var (s,t) ) = s ^ ":" ^ mkTy t
   | ppexpr ( Deref e ) = "(!" ^ ppexpr e ^ ")"
   | ppexpr ( UMinus e ) = "~" ^ ppexpr e
   | ppexpr ( BinOp (e1,oper,e2) ) = "(" ^ ppexpr e1 ^ " " ^ ppopr oper ^ " " ^ ppexpr e2 ^ ")"
   | ppexpr ( BNot e ) = "not " ^ ppexpr e
   | ppexpr ( If (cl,tc,fc) ) = "if " ^ ppexpr cl ^ " then " ^ ppexpr tc ^ " else " ^ ppexpr fc
   | ppexpr ( Let (s,e1,e2) ) = "let " ^ s ^ "=" ^ ppexpr e1 ^ " in " ^ ppexpr e2
   | ppexpr ( Seq (e1,e2) ) = ppexpr e1 ^ " ; " ^ ppexpr e2
   | ppexpr ( TypeAnnotation (e,t) ) = ppexpr e ^ ":" ^ ppty t
   | ppexpr ( Tuple l ) = "(" ^ ppels l ^ ")"
   | ppexpr ( List l ) = "[" ^ ppels l ^ "]"
   | ppexpr ( App (e1,e2) ) = ppexpr e1 ^ " (" ^ ppexpr e2 ^ ")"
   | ppexpr ( True ) = "true"
   | ppexpr ( False ) = "false"
   and ppels [] = ""
     | ppels (h::[]) = ppexpr h
     | ppels (h::t) = ppexpr h ^ "," ^ ppels t
   and ppstm (ValBinding ((s,t), e)) = "val " ^ s ^ " : " ^ mkTy t ^ " = " ^ ppexpr e
   | ppstm (TyBinding (s, t)) = "type " ^ s ^ " = " ^ ppty t
   | ppstm (DatatypeBinding k) = "datatype ..."
   | ppstm (StructBinding (s,stms)) = "structure " ^ s ^ " = struct\n" ^ ppstmlist stms ^ "\nend"
   | ppstm (SigBinding k) = "signature ..."
   and ppstmlist [] = ""
     | ppstmlist (h::t) = ppstm h ^ "\n" ^ ppstmlist t

end

