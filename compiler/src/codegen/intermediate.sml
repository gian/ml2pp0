structure Intermediate =
struct
	open Ast

	type name = int
	type symbol = Symbol.symbol

	datatype store = Reg of int
	               | Name of int
				   | IntImm of int
				   | Label of int

	val rc = ref 0
	val nc = ref 0
	val lc = ref 0

	val env = ref [] : (int * store) list ref

	fun lookup' i = List.find (fn (m,_) => i = m) (!env) 

	fun lookup s = (fn NONE => NONE | (SOME (x,y)) => SOME y) 
						(lookup' (Symbol.hash s))

	fun insert s r = env := (Symbol.hash s,r) :: !env

	fun register () = Reg (rc := !rc + 1; !rc)
	fun name () = Name (nc := !nc + 1; !nc)
	fun label () = (lc := !lc + 1; !lc)

	datatype ir =
		ADD of store * store * store
	  |	ADDI of store * store * int
	  |	AND of store * store * store 
	  |	ANDI of store * store * int
	  | ICMP of store * string * store * store 
	  |	SUB of store * store * store
	  |	SUBI of store * store * int
	  | DIV of store * store * store
	  | DIVI of store * store * int
	  |	MUL of store * store * store
	  |	MULI of store * store * int
	  |	MOV of store * store
	  | PHI of store * Ast.ty * (store * int) * (store * int)
	  |	LABEL of int 
	  | LIT_INT of int
	  | CBR of store * int * int
	  | BR of int
	  | RET of Ast.ty * store
	  | CALL of store * store * store
	  | FUNCTION of store * Ast.ty * (store * Ast.ty) list * ir list
	  | UnconvertedExp of Ast.exp

	val funs = ref [] : ir list ref

	fun trans_e (BinOp {opr=p,lhs,rhs,...}) r3 =
		let
			val r1 = register ()
			val r2 = register ()
			val (r1',i1) = trans_e lhs r1
			val (r2',i2) = trans_e rhs r2
			val cn = 
				(case p of Plus => [ADD (r3, r1', r2')]
			             | Minus => [SUB (r3, r1', r2')]
						 | Times => [MUL (r3, r1', r2')]
						 | Div => [DIV (r3, r1', r2')]
						 | Equal => [ICMP (r3, "eq", r1', r2')]
						 | NEqual => [ICMP (r3, "ne", r1', r2')]
						 | GT => [ICMP (r3, "sgt", r1', r2')]
						 | LT => [ICMP (r3, "slt", r1', r2')]
						 | GTEqual => [ICMP (r3, "sge", r1', r2')]
						 | LTEqual => [ICMP (r3, "sle", r1', r2')]
						 | _ => raise Fail "Unhandled binop")
		in
			(r3, i1 @ i2 @ cn)
		end
	  | trans_e (Var {name,symtab,...}) r3 =
	  	let
			val _ = print "CODEGEN: Var\n"
			val r = case lookup name of NONE => 
						let
							val r' = register ()
							val _ = insert name r'
							(* TODO Do lookup here.
								Should check for function type, and return name and types. *)
						in
							r'
						end
					   | (SOME x) => x
		in
			(r,[])
		end
	  | trans_e (Fn {attr,match,symtab}) fname =
	  	let
			val _ = print "CODEGEN: Fn\n"

			val f = hd match (* FIXME process more than one clause *)
			
			val ty = Types.tyInt
			val pat = (case (#1 f) of
						VarPat {attr,name,symtab} => let
							val r = register ()
							val _ = insert name r
						in
							[(r,Types.tyInt)]
						end
						| _ => raise Fail "Unhandled pat in codegen")

			val ret = register ()

			val (ret',body) = trans_e (#2 f) ret
			val body' = body @ [RET (Types.tyInt,ret')]

			val _ = funs := !funs @ [FUNCTION (fname,ty,pat,body')]
		in
			(fname, [])
		end
	  | trans_e (App {exps=[f,x],...}) res = 
	  	let
			val _ = print "APP!\n"
			val r1 = register ()
			val r2 = register ()
			val (r2',i2) = trans_e f r2
			val (r1',i1) = trans_e x r1
		in
			(res, i2 @ i1 @ [CALL (res, r2', r1')])
		end
	  | trans_e (If {attr,cond,tbr,fbr}) res = 
	  	let
			val (cond',ci) = trans_e cond (register ())
			val (tbr',tci) = trans_e tbr (register ())
			val (fbr',fci) = trans_e fbr (register ())

			val tlab = label ()
			val flab = label ()
			val phi = label ()

			val bri = [CBR (cond', tlab, flab)]

			val phii = [PHI (res, Types.tyInt, (tbr',tlab), (fbr',flab))]
		in
			(res, 
				ci
			  @ bri
			  @	[LABEL tlab]
			  @ tci
			  @ [BR phi]
			  @ [LABEL flab]
			  @ fci
			  @ [BR phi]
			  @ [LABEL phi]
			  @ phii
			)
		end
	  | trans_e (p as App x) res = raise Fail ("APP: " ^ PrettyPrint.ppexp p)
	  | trans_e (Int i) r =
			(r, [ADD (r,IntImm 0,IntImm i)])
	  | trans_e x res = (register(), [UnconvertedExp x])

	fun emit_r (Reg i) = "%r" ^ Int.toString i
	  | emit_r (Name i) = "@anon_" ^ Int.toString i
	  | emit_r (Label i) = "%lab" ^ Int.toString i
	  | emit_r (IntImm i) = Int.toString i

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
	  | emit' (RET (t,r)) = "ret " ^ emit_ty t ^ " " ^ emit_r r
	  | emit' (LABEL l) = "lab" ^ Int.toString l ^ ":"
	  | emit' (ICMP (r,opr,o1,o2)) = emit_r r ^ " = icmp " ^ opr ^ 
	  									" i32 " ^ emit_r o1 ^ ", " ^
										emit_r o2
	  | emit' (CBR (s,l1,l2)) = "br i1 " ^ emit_r s ^ ", label %lab" ^
	  							Int.toString l1 ^ ", label %lab" ^
								Int.toString l2
	  | emit' (BR i) = "br label %lab" ^ Int.toString i
	  | emit' (PHI (ret,ty,(r1,l1),(r2,l2))) =
	  		emit_r ret ^ " = phi " ^ emit_ty ty ^ " [ " ^ 
				emit_r r1 ^ ", %lab" ^ Int.toString l1 ^ " ], [ " ^
				emit_r r2 ^ ", %lab" ^ Int.toString l2 ^ " ]"
	  | emit' (FUNCTION (n,rt,args,body)) = 
	  	"define fastcc " ^ emit_ty rt ^ " " ^
		emit_r n ^ "(" ^
		(String.concatWith "," 
			(map (fn (x,t) => emit_ty t ^ " " ^ emit_r x) args)) ^
		") {\n\t\tentry:\n\t\t" ^ 
		(String.concatWith "\n\t\t" (map emit' body)) ^
		"\n\t}"
	  | emit' (CALL (rt,f,a)) = 
	  	emit_r rt ^ " = call fastcc i32 " ^ emit_r f ^ "(i32 " ^ emit_r a ^ ")"
	  | emit' _ = "# unemitted"

	fun emit_bd [] = "\n"
	  | emit_bd (h::t) = "\t" ^ emit' h ^ "\n" ^ emit_bd t

	fun emit l =
		emit_bd (!funs) ^ 
		"\n\ndefine fastcc i32 @ml_main() {\nentry:\n" ^ emit_bd l ^ "\n\tret i32 0\n}\n"

	fun translate symtab =
		let
			val {venv,tenv} = !symtab

			val vkeys = Symbol.keys (!venv)
		in
			List.foldl (fn ((s,(t,SOME e)),instr) =>
				let
					val _ = print ("Translating " ^ Symbol.toString (valOf (Symbol.unhash s)) ^ " = " ^ PrettyPrint.ppexp e ^ "\n")

					val forwardSymbol = 
						(case t of NONE => raise Fail ("Translate found unknown symbol")
						         | (SOME (ArrowTy _)) => name ()
								 | (SOME _) => register ())
										

					val _ = insert (valOf (Symbol.unhash s)) forwardSymbol 
					val (r,i) = trans_e e forwardSymbol

				in
					i @ instr
				end
				| (_,instr) => instr) [] vkeys
		end
end

