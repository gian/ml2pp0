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
	  |	SUB of register * register * register
	  |	SUBI of register * register * int
	  |	LOADI of register * int
	  |	BRZ of label
	  |	BRNZ of label
	  |	MUL of register * register * register
	  |	MOV of register * register
	  |	LABEL of label
	  | UnconvertedDec of Ast.dec
	  | UnconvertedExp of Ast.exp

	fun translate (ValDec v) =
		(case (hd (#valBind v)) of
			(ValBind (Wild,e)) => trans_e e)
	  | translate d = (register(), [UnconvertedDec d])
	and trans_e (BinOp {opr=Plus,lhs,rhs,...}) =
		let 
			val (r1,i1) = trans_e lhs
			val (r2,i2) = trans_e rhs
			val r3 = register ()
		in
			(r3, i1 @ i2 @ [ADD (r3, r1, r2)])
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
	  | trans_e x = (register(),[UnconvertedExp x])


	fun emit_r i = "$" ^ Int.toString i

	fun emit' (ADD (r1,r2,r3)) = "add " ^ emit_r r1 ^ " " ^
										 emit_r r2 ^ " " ^
										 emit_r r3 ^ "\n"
	  | emit' _ = "# unemitted\n"

	fun emit [] = ""
	  | emit (h::t) = emit' h ^ emit t
end

