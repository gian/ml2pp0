structure Intermediate =
struct
	open Ast

	type register = int
	type label = int
	type symbol = Symbol.symbol

	val rc = ref 0

	val env = ref [] : (int * register) list ref

	fun lookup' i = List.find (fn (_,m) => i = m) (!env) 

	fun lookup s = (fn NONE => NONE | (SOME (x,y)) => SOME y) 
						(lookup' (Symbol.hash s))

	fun insert s r = env := (Symbol.hash s,r) :: !env

	fun register () = (rc := !rc + 1; !rc)

	datatype ir =
		ADD of register * register * register
	  |	ADDI of register * register * int
	  |	AND of register * register * register 
	  |	ANDI of register * register * int
	  |	SUB of register * register * register
	  |	SUBI of register * register * int
	  | DIV of register * register * register
	  | DIVI of register * register * int
	  |	BRZ of label
	  |	BRNZ of label
	  |	MUL of register * register * register
	  |	MULI of register * register * int
	  |	MOV of register * register
	  |	LABEL of label
	  | UnconvertedDec of Ast.dec
	  | UnconvertedExp of Ast.exp

	fun translate (ValDec v) =
		(case (hd (#valBind v)) of
			(ValBind (Wild,e)) => trans_e e
		  | (ValBind (_,e)) => trans_e e
		  | b => (register(),[UnconvertedDec (ValDec v)]))
	  | translate d = (register(), [UnconvertedDec d])
	and trans_e (BinOp {opr=p,lhs,rhs=Int i,...}) =
		let 
			val (r1,i1) = trans_e lhs
			val r3 = register ()
			val cn = 
				(case p of Plus => [ADDI (r3, r1, i)]
			             | Minus => [SUBI (r3, r1, i)]
						 | Times => [MULI (r3, r1, i)]
						 | Div => [DIVI (r3, r1, i)]
						 | Equal => [ANDI (r3, r1, i)])
		in
			(r3, i1 @ cn)
		end
	  | trans_e (BinOp {opr=p,lhs,rhs,...}) =
		let 
			val (r1,i1) = trans_e lhs
			val (r2,i2) = trans_e rhs
			val r3 = register ()
			val cn = 
				(case p of Plus => [ADD (r3, r1, r2)]
			             | Minus => [SUB (r3, r1, r2)]
						 | Times => [MUL (r3, r1, r2)]
						 | Div => [DIV (r3, r1, r2)]
						 | Equal => [AND (r3, r1, r2)])
		in
			(r3, i1 @ i2 @ cn)
		end
	  | trans_e (Var {name,...}) =
	  	let
			val r = case lookup name of NONE => 
						let
							val r' = register()
							val _ = insert name r'
						in
							r'
						end
					   | (SOME x) => x
		in
			(r,[])
		end
	  | trans_e (Int i) =
	  	let
			val r = register ()
		in
			(r, [ADDI (r, 0, i)])
		end


	fun emit_r i = "$" ^ Int.toString i

	fun emit' (ADD (r1,r2,r3)) = "\tadd\t" ^ emit_r r1 ^ "\t" ^
										 emit_r r2 ^ "\t" ^
										 emit_r r3
	  | emit' (ADDI (r1,r2,v)) = "\taddi\t" ^ emit_r r1 ^ "\t" ^ 
	  									emit_r r2 ^ "\t" ^ 
	  									Int.toString v
	  | emit' (SUB (r1,r2,r3)) = "\tsub\t" ^ emit_r r1 ^ "\t" ^
										 emit_r r2 ^ "\t" ^
										 emit_r r3
	  | emit' (SUBI (r1,r2,v)) = "\tsubi\t" ^ emit_r r1 ^ "\t" ^ 
	  									emit_r r2 ^ "\t" ^ 
	  									Int.toString v 
	  | emit' (MUL (r1,r2,r3)) = "\tmul\t" ^ emit_r r1 ^ "\t" ^
										 emit_r r2 ^ "\t" ^
										 emit_r r3
	  | emit' (MULI (r1,r2,v)) = "\tmuli\t" ^ emit_r r1 ^ "\t" ^ 
	  									emit_r r2 ^ "\t" ^ 
	  									Int.toString v 
	  | emit' (AND (r1,r2,r3)) = "\tand\t" ^ emit_r r1 ^ "\t" ^
										 emit_r r2 ^ "\t" ^
										 emit_r r3
	  | emit' (ANDI (r1,r2,v)) = "\tandi\t" ^ emit_r r1 ^ "\t" ^ 
	  									emit_r r2 ^ "\t" ^ 
	  									Int.toString v 
	  | emit' (UnconvertedDec d) = "# dec: "^ PrettyPrint.prettyPrint [d] ^ "\n"
	  | emit' (UnconvertedExp e) = "# exp: " ^ PrettyPrint.ppexp e ^ "\n"
	  | emit' _ = "# unemitted\n"

	fun emit [] = ""
	  | emit (h::t) = emit' h ^ "\n" ^ emit t
end

