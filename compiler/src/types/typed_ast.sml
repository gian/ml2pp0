(* Typed abstract syntax tree *)
structure TypedAST =
struct
   open Absyn

   datatype 'a ast = Node of 'a * 'a ast list
                   | Leaf of 'a

   datatype oper =
      Integer 
   |  String
   |  AnonFn
   |  Nil
   |  Unit
   |  Var of string
   |  Deref
   |  UMinus
   |  BinOp of Absyn.opr
   |  BNot
   |  If
   |  Let of string
   |  Seq
   |  TypeAnnotation
   |  Tuple
   |  List
   |  App
   |  Boolean 
   |  ValBinding of string

   type typed = oper * ty

   fun substinty (TyVar x1) tyT tyS =
     let
        fun f tyS =
         (case tyS of (TyArrow(tyS1,tyS2)) => (TyArrow(f tyS1,f tyS2))
                    | (TyVar n) => if n = x1 then tyT else (TyVar n)
                    | (TyName s) => TyName s
                    | (LVar s) => LVar s
                    | (TyPoly s) => TyPoly s
                    | (TyCon (tyS1,tyS2)) => (TyCon (f tyS1, f tyS2))
                    | TyNil => TyNil)
     in
        f tyS
     end
     | substinty (TyPoly x1) tyT tyS =
     let
         fun f tyS =
         (case tyS of (TyArrow(tyS1,tyS2)) => (TyArrow(f tyS1,f tyS2))
                    | (TyVar n) => (TyVar n)
                    | (TyName s) => TyName s
                    | (LVar s) => LVar s
                    | (TyPoly s) => if s=x1 then tyT else TyPoly s
                    | (TyCon (tyS1,tyS2)) => (TyCon (f tyS1, f tyS2))
                    | TyNil => TyNil)
     in
        f tyS
     end
     | substinty t1 t2 t3 =
       raise Fail ("Unhandled subst: " ^ Absyn.ppty t1 ^ ", " ^ Absyn.ppty t2 ^ ", " ^ Absyn.ppty t3)

   fun substinTypedAst tyS tyR (Leaf (v,tyO)) = Leaf (v,substinty tyS tyR tyO)
     | substinTypedAst tyS tyR (Node ((v,tyO), ch)) = 
         Node ((v,substinty tyS tyR tyO), map (substinTypedAst tyS tyR) ch)

   (* Pretty Debug.print_dbg code follows *)
   fun pptypednode Integer = "Integer"
     | pptypednode String = "String"
     | pptypednode AnonFn = "AnonFn"
     | pptypednode Nil = "Nil"
     | pptypednode Unit = "Unit"
     | pptypednode (Var s) = "Var " ^ s
     | pptypednode Deref = "Deref"
     | pptypednode UMinus = "UMinus"
     | pptypednode (BinOp opr) = "op " ^ Absyn.ppopr opr
     | pptypednode BNot = "BNot"
     | pptypednode If = "If"
     | pptypednode (Let s) = "Let " ^ s
     | pptypednode Seq = "Seq"
     | pptypednode TypeAnnotation = "TypeAnnotation"
     | pptypednode Tuple = "Tuple"
     | pptypednode List = "List"
     | pptypednode App  = "App"
     | pptypednode Boolean = "Boolean"
     | pptypednode (ValBinding s) = "ValBinding " ^ s

   fun pptypedast_h (Leaf (Integer,_)) = "<integer>"
     | pptypedast_h (Leaf (String,_)) = "<string>"
     | pptypedast_h (Leaf (Nil,_)) = "nil"
     | pptypedast_h (Leaf (Unit,_)) = "()"
     | pptypedast_h (Leaf (Var s,t)) = "<var " ^ s ^ "> : " ^ Absyn.ppty t
     | pptypedast_h (Leaf _) = "INVALID LEAF"
     | pptypedast_h (Node ((ValBinding s, t), [c1])) = "val " ^ s ^ " : " ^ Absyn.ppty t ^ " = " ^ pptypedast_h c1 ^ "\n"
     | pptypedast_h (Node ((nt, t), children)) = 
       pptypednode nt ^ " : " ^ Absyn.ppty t ^ " [" ^ String.concatWith "," (map pptypedast_h children) ^ "]"

   fun pptypedast [] = ""
     | pptypedast (h::t) = pptypedast_h h ^ ";\n" ^ pptypedast t

end

