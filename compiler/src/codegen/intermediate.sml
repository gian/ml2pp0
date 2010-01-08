structure Intermediate =
struct
	open Ast

	type label = int
	type symbol = Symbol.symbol

	datatype store = SRegister of int
				   | VRegister of int * int
	               | LocalMem of label
				   | GlobalMem of label
				   | NullStore
	
	val rc = ref 0
	val lc = ref 0

	val env = ref [] : (int * store) list ref

	fun lookup' i = List.find (fn (m,_) => i = m) (!env) 

	fun lookup s = (fn NONE => NONE | (SOME (x,y)) => SOME y) 
						(lookup' (Symbol.hash s))

	fun insert s r = env := (Symbol.hash s,r) :: !env

	fun scalar_store () = SRegister (rc := !rc + 1; !rc)
	fun label () = (lc := !lc + 1; !lc)

	datatype ir =
		ADD of store * store * store
	  |	ADDI of store * store * int
	  |	AND of store * store * store 
	  |	ANDI of store * store * int
	  |	SUB of store * store * store
	  |	SUBI of store * store * int
	  | DIV of store * store * store
	  | DIVI of store * store * int
	  |	BRZ of label
	  |	BRNZ of label
	  |	MUL of store * store * store
	  |	MULI of store * store * int
	  |	MOV of store * store
	  |	LABEL of label
	  | LIT_INT of int
	  | UnconvertedDec of Ast.dec
	  | UnconvertedExp of Ast.exp

	fun trans_d (ValDec v) =
		(case (hd (#valBind v)) of
		    (ValBind (_,e)) => trans_e e
		  | b => (scalar_store(),[UnconvertedDec (ValDec v)], []))
	  | trans_d (FunDec f) = (NullStore, [LABEL (label())], [])
	  | trans_d d = (scalar_store(), [UnconvertedDec d], [])
	and trans_e (BinOp {opr=p,lhs,rhs,...}) =
		let 
			val (r1,i1,d1) = trans_e lhs
			val (r2,i2,d2) = trans_e rhs
			val r3 = scalar_store ()
			val cn = 
				(case p of Plus => [ADD (r3, r1, r2)]
			             | Minus => [SUB (r3, r1, r2)]
						 | Times => [MUL (r3, r1, r2)]
						 | Div => [DIV (r3, r1, r2)]
						 | Equal => [AND (r3, r1, r2)]
						 | _ => raise Fail "Unhandled binop")
		in
			(r3, i1 @ i2 @ cn, d1 @ d2)
		end
	  | trans_e (Var {name,...}) =
	  	let
			val r = case lookup name of NONE => 
						let
							val r' = scalar_store()
							val _ = insert name r'
						in
							r'
						end
					   | (SOME x) => x
		in
			(r,[], [])
		end
	  | trans_e (Int i) =
	  	let
			val r = label ()
		in
			(LocalMem r, [], [LABEL r, LIT_INT i])
		end
	  | trans_e x = (scalar_store(), [UnconvertedExp x], [])

	fun translate [] = []
	  | translate (h::t) = trans_d h :: translate t


	fun emit_r (SRegister i) = "S" ^ Int.toString i
      | emit_r (VRegister (i,_)) = "V" ^ Int.toString i
      | emit_r (LocalMem i) = "[L" ^ Int.toString i ^ "]"
      | emit_r (GlobalMem i) = "(" ^ Int.toString i ^ ")"
	  | emit_r (NullStore) = "<NULLSTORE (error)>"

	fun emit' (ADD (r1,r2,r3)) = emit_r r1 ^ " " ^
										 emit_r r2 ^ "+" ^
										 emit_r r3
	  | emit' (ADDI (r1,r2,v)) = emit_r r1 ^ " " ^ 
	  									emit_r r2 ^ "+" ^ 
	  									Int.toString v
	  | emit' (SUB (r1,r2,r3)) = emit_r r1 ^ " " ^
										 emit_r r2 ^ "-" ^
										 emit_r r3
	  | emit' (SUBI (r1,r2,v)) = emit_r r1 ^ " " ^ 
	  									emit_r r2 ^ "-" ^ 
	  									Int.toString v 
	  | emit' (MUL (r1,r2,r3)) = emit_r r1 ^ " " ^
										 emit_r r2 ^ "*" ^
										 emit_r r3
	  | emit' (MULI (r1,r2,v)) = emit_r r1 ^ " " ^ 
	  									emit_r r2 ^ "*" ^ 
	  									Int.toString v 
	  | emit' (AND (r1,r2,r3)) = emit_r r1 ^ " " ^
										 emit_r r2 ^ "&" ^
										 emit_r r3
	  | emit' (ANDI (r1,r2,v)) = emit_r r1 ^ " " ^ 
	  									emit_r r2 ^ "&" ^ 
	  									Int.toString v 
	  | emit' (LABEL l) = "L" ^ Int.toString l ^ ":"
	  | emit' (LIT_INT i) = Int.toString i
	  | emit' (UnconvertedDec d) = "# dec: "^ PrettyPrint.prettyPrint [d] ^ "\n"
	  | emit' (UnconvertedExp e) = "# exp: " ^ PrettyPrint.ppexp e ^ "\n"
	  | emit' _ = "# unemitted\n"

	fun emito [] = ""
	  | emito ((LABEL l)::t) = (emit' (LABEL l)) ^ emito t
	  | emito (h::t) = "\t\t\t" ^ emit' h ^ "\n" ^ emito t

	fun emit [] t d = ".text\n" ^ emito t ^ "\n.data\n" ^ emito d
	  | emit ((_,t',d')::r) t d = emit r (t@t') (d@d')

end

