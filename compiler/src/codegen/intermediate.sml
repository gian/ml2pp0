structure Intermediate =
struct
	open Ast

	type label = int
	type symbol = Symbol.symbol

	type store = int

	val rc = ref 0
	val lc = ref 0

	val env = ref [] : (int * store) list ref

	fun lookup' i = List.find (fn (m,_) => i = m) (!env) 

	fun lookup s = (fn NONE => NONE | (SOME (x,y)) => SOME y) 
						(lookup' (Symbol.hash s))

	fun insert s r = env := (Symbol.hash s,r) :: !env

	fun register () = (rc := !rc + 1; !rc)
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
	  | FUNCTION of int * Ast.ty * ir list
	  | UnconvertedExp of Ast.exp

	fun trans_e (BinOp {opr=p,lhs,rhs,...}) =
		let 
			val (r1,i1) = trans_e lhs
			val (r2,i2) = trans_e rhs
			val r3 = register ()
			val cn = 
				(case p of Plus => [ADD (r3, r1, r2)]
			             | Minus => [SUB (r3, r1, r2)]
						 | Times => [MUL (r3, r1, r2)]
						 | Div => [DIV (r3, r1, r2)]
						 | Equal => [AND (r3, r1, r2)]
						 | _ => raise Fail "Unhandled binop")
		in
			(r3, i1 @ i2 @ cn)
		end
	  | trans_e (Var {name,...}) =
	  	let
			val r = case lookup name of NONE => 
						let
							val r' = register ()
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
			val r = label ()
		in
			(r, [ADDI (r,0,i)])
		end
	  | trans_e x = (register(), [UnconvertedExp x])

	fun emit_r i = "%" ^ Int.toString i

	fun emit_ty x = "i32"

	fun fmt instr ty (a,b,c) =
		emit_r a ^ " = " ^ 
				   instr ^ 
				   	 " " ^ 
			  emit_ty ty ^ 
			         " " ^
				emit_r b ^
				     "," ^
			    emit_r c 

	fun emit' (ADD ops) = fmt "add" "i32" ops 
	  | emit' (SUB ops) = fmt "sub" "i32" ops
	  | emit' (MUL ops) = fmt "mul" "i32" ops
	  | emit' (AND ops) = fmt "and" "i32" ops
	  | emit' _ = "# unemitted"

	fun emit [] = "\n"
	  | emit (h::t) = "\t\t\t" ^ emit' h ^ "\n"

	fun translate symtab =
		let
			val {venv,tenv} = !symtab

			val vkeys = Symbol.keys (!venv)
		in
			List.foldl (fn ((s,(t,SOME e)),instr) =>
				let
					val (r,i) = trans_e e
				in
					i @ instr
				end) [] vkeys
		end
end

