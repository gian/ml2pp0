structure Intermediate =
struct
	open Ast
	open Types

	type name = int
	type symbol = Symbol.symbol

	datatype store = Reg of int * Ast.ty
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

	fun register (ty) = Reg ((rc := !rc + 1; !rc), Types.tyInt)
	fun name () = Name (nc := !nc + 1; !nc)
	fun label () = (lc := !lc + 1; !lc)

	fun setTy t (Reg (d,_)) = Reg (d, t)
	  | setTy t _ = raise Fail "setTy called on non-register"

	fun getTy (Reg (_,t)) = t
	  | getTy _ = raise Fail "getTy called on non-register"

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
	  | LIT_STRING of store * string
	  | ELPTR of store * int * string * store * int * int
	  | CBR of store * int * int
	  | BR of int
	  | RET of Ast.ty * store
	  | CALL of store * store * store
	  | FUNCTION of store * Ast.ty * (store * Ast.ty) list * ir list
	  | UnconvertedExp of Ast.exp

	val funs = ref [] : ir list ref

	fun trans_e (BinOp {opr=p,lhs,rhs,...}) r3 =
		let
			val r1 = register (tyInt)
			val r2 = register (tyInt)
			val (r1',i1) = trans_e lhs r1
			val (r2',i2) = trans_e rhs r2
			val cn = 
				(case p of Plus => [ADD (setTy tyInt r3, r1', r2')]
			       	 | Minus => [SUB (setTy tyInt r3, r1', r2')]
					 | Times => [MUL (setTy tyInt r3, r1', r2')]
					 | Div => [DIV (setTy tyInt r3, r1', r2')]
					 | Equal => [ICMP (setTy tyBool r3, "eq", r1', r2')]
					 | NEqual => [ICMP (setTy tyBool r3, "ne", r1', r2')]
					 | GT => [ICMP (setTy tyBool r3, "sgt", r1', r2')]
					 | LT => [ICMP (setTy tyBool r3, "slt", r1', r2')]
					 | GTEqual => [ICMP(setTy tyBool r3, "sge", r1', r2')]
					 | LTEqual => [ICMP(setTy tyBool r3, "sle", r1', r2')]
					 | _ => raise Fail "Unhandled binop")
		in
			(setTy tyInt r3, i1 @ i2 @ cn)
		end
	  | trans_e (Var {name,symtab,...}) r3 =
	  	let
			val _ = print "CODEGEN: Var\n"
			val r = case lookup name of NONE => 
						let
							val r' = register (tyInt)

							val (t,s) = Symtab.lookup_v symtab name

							val r'' = (case t of NONE => r'
							                   | SOME t => setTy t r')
							
							val _ = insert name r''
						in
							r''
						end
					   | (SOME x) => x
		in
			(r,[])
		end
	  | trans_e (Fn {attr,match,symtab,ty=SOME ty}) fname =
	  	let
			val _ = print "CODEGEN: Fn\n"

			val f = hd match (* FIXME process more than one clause *)
		
			val (pTy,retTy) = (case ty of ArrowTy (pt,rt) => (pt,rt)
			                | _ => raise Fail "Non-arrow type in Fn")

			val pat = (case (#1 f) of
						VarPat {attr,name,symtab} => let
							val r = register (pTy)
							val _ = insert name r
						in
							[(r,pTy)]
						end
						| _ => raise Fail "Unhandled pat in codegen")

			val ret = register retTy

			val (ret',body) = trans_e (#2 f) ret
			val body' = body @ [RET (retTy,ret')]

			val _ = funs := !funs @ [FUNCTION (fname,retTy,pat,body')]
		in
			(fname, [])
		end
	  | trans_e (App {exps=[f,x],...}) res = 
	  	let
			val _ = print "APP!\n"
			val r1 = register (tyInt)
			val r2 = register (tyInt)
			val (r2',i2) = trans_e f r2
			val (r1',i1) = trans_e x r1
		in
			(res, i2 @ i1 @ [CALL (res, r2', r1')])
		end
	  | trans_e (BuiltIn s) r = (r, []) 
	  | trans_e (If {attr,cond,tbr,fbr}) res = 
	  	let
			val (cond',ci) = trans_e cond (register tyBool)
			val (tbr',tci) = trans_e tbr (register tyInt)
			val (fbr',fci) = trans_e fbr (register tyInt)

			val tlab = label ()
			val flab = label ()
			val phi = label ()

			val bri = [CBR (cond', tlab, flab)]

			val phii = [PHI (res, getTy tbr', (tbr',tlab), (fbr',flab))]
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
			(setTy tyInt r, [ADD (setTy tyInt r,IntImm 0,IntImm i)])
	  | trans_e (String s) r =
	  	let
			val r' = setTy tyString r

			val n = name ()

	  		val _ = funs := !funs @ [LIT_STRING (n,s)]
		in
			(r', [ELPTR (r', 1 + size s, "i8", n, 0, 0)])
		end
	  | trans_e x res = (register tyInt, [UnconvertedExp x])

	fun emit_r (Reg (i,t)) = "%r" ^ Int.toString i
	  | emit_r (Name i) = "@anon_" ^ Int.toString i
	  | emit_r (Label i) = "%lab" ^ Int.toString i
	  | emit_r (IntImm i) = Int.toString i

	fun emit_ty t = if PrettyPrint.ppty t = "string" then "i8 *"
	 		   else if PrettyPrint.ppty t = "bool" then "i1"
			   else "i32"

	fun fmt instr ty (a,b,c) =
		emit_r a ^ " = " ^ 
				   instr ^ 
				   	 " " ^ 
			  emit_ty ty ^ 
			         " " ^
				emit_r b ^
				     "," ^
			    emit_r c 

	fun emit' (ADD ops) = fmt "add" tyInt ops 
	  | emit' (SUB ops) = fmt "sub" tyInt ops
	  | emit' (MUL ops) = fmt "mul" tyInt ops
	  | emit' (AND ops) = fmt "and" tyInt ops
	  | emit' (RET (t,r)) = "ret " ^ emit_ty t ^ " " ^ emit_r r
	  | emit' (LABEL l) = "lab" ^ Int.toString l ^ ":"
	  | emit' (ICMP (r,opr,o1,o2)) = emit_r r ^ " = icmp " ^ opr ^ " " ^
	  								emit_ty (getTy o1) ^ " " ^ 
									emit_r o1 ^ ", " ^
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
	  | emit' (ELPTR (r,els,sz,src,o1,o2)) =
	  	emit_r r ^ " = getelementptr [" ^ Int.toString els ^ " x " ^ sz ^
				   "]* " ^ emit_r src ^ ", i64 " ^ Int.toString o1 ^
				   ", i64 " ^ Int.toString o2 
	  | emit' (LIT_STRING (n,s)) = emit_r n ^ 
	  	" = private constant [" ^ Int.toString (1+size s) ^ " x i8] c\"" ^
		String.toCString s ^ "\\00\", align 1"
	  | emit' (CALL (rt,f,a)) = 
	  	emit_r rt ^ " = call fastcc " ^
			emit_ty (getTy rt) ^ " " ^
			emit_r f ^ "(" ^ 
			emit_ty (getTy a) ^ " " ^
			emit_r a ^ ")"
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
								 | (SOME _) => register tyInt)
										

					val _ = insert (valOf (Symbol.unhash s)) forwardSymbol 
					val (r,i) = trans_e e forwardSymbol

				in
					i @ instr
				end
				| (_,instr) => instr) [] vkeys
		end
end

