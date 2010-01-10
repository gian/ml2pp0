structure Intermediate =
struct
	open Ast
	open Types

	type symbol = Symbol.symbol

	datatype store = Reg of int * Ast.ty
	               | Name of int * Ast.ty
				   | IntImm of int
				   | Label of int
				   | BuiltInName of string * Ast.ty
				   | Null

	val rc = ref 0
	val nc = ref 0
	val lc = ref 0

	val env = ref [] : (int * store) list ref

	fun lookup' i = List.find (fn (m,_) => i = m) (!env) 

	fun lookup s = (fn NONE => NONE | (SOME (x,y)) => SOME y) 
						(lookup' (Symbol.hash s))

	fun insert s r = env := (Symbol.hash s,r) :: !env

	val _ = insert (Symbol.fromString "puts") (BuiltInName ("puts",
				Ast.ArrowTy (tyString,tyInt)))

	val _ = insert (Symbol.fromString "hd") (BuiltInName ("hd",
				Ast.ArrowTy (Ast.ListTy (Ast.PolyTy 0), Ast.PolyTy 0)))

	val _ = insert (Symbol.fromString "tl") (BuiltInName ("tl",
				Ast.ArrowTy	(Ast.ListTy (Ast.PolyTy 0), 
							 Ast.ListTy (Ast.PolyTy 0))))

	fun register (ty) = Reg ((rc := !rc + 1; !rc), ty)
	fun name (ty) = Name ((nc := !nc + 1; !nc), ty)
	fun label () = (lc := !lc + 1; !lc)

	fun setTy t (Reg (d,_)) = Reg (d, t)
	  | setTy t _ = raise Fail "setTy called on non-register"

	fun getTy (Reg (_,t)) = t
	  | getTy (BuiltInName (s,t)) = t
	  | getTy (Name (i,t)) = t 
	  | getTy (Label i) = raise Fail "getTy called on Label"
	  | getTy (IntImm i) = raise Fail "getTy called on IntImm"

	datatype ir =
		ADD of store * store * store
	  |	ADDI of store * store * int
	  |	AND of store * store * store 
	  |	ANDI of store * store * int
	  | BR of int
	  | CALL of store * store * store
	  | CBR of store * int * int
	  | CONS of store * store * store
	  | DIV of store * store * store
	  | DIVI of store * store * int
	  | ELPTR of store * int * string * store * int * int
	  | FUNCTION of store * Ast.ty * (store * Ast.ty) list * ir list
	  | ICMP of store * string * store * store 
	  |	LABEL of int 
	  | LIT_INT of int
	  | LIT_STRING of store * string
	  |	MUL of store * store * store
	  |	MULI of store * store * int
	  |	MOV of store * store
	  | PHI of store * Ast.ty * (store * int) * (store * int)
	  | RET of Ast.ty * store
	  |	SUB of store * store * store
	  |	SUBI of store * store * int
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
					 | Cons => [CONS (setTy (Ast.ListTy (getTy r1')) r3,
					 				  r1', r2')]
					 | _ => raise Fail "Unhandled binop")
		in
			(setTy tyInt r3, i1 @ i2 @ cn)
		end
	  | trans_e (Var {name,symtab,...}) r3 =
	  	let
			val _ = print ("CODEGEN: Var " ^ Symbol.toString name ^ "\n")
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
					   | (SOME (Reg x)) => (Reg x)
					   | (SOME (Name (x,Ast.ArrowTy(t1,t2)))) =>
					   	let
							val par = register t1
							val ret = register t2

							val _ = funs := !funs @
							[FUNCTION (
								Name (x,Ast.ArrowTy(t1,t2)),
								t2,
								[(par, t1)],
								[
									CALL (ret, 
										  Name(x,Ast.ArrowTy (t1,t2)), 
										  par),
									RET (t2, ret)
								])
							]
						in
							(Name (x,Ast.ArrowTy(t1,t2)))
						end
					   | (SOME x) => x 

			val _ = print ("Var has type: " ^ PrettyPrint.ppty (getTy r) ^ "\n")
		in
			(r,[])
		end
	  | trans_e (BuiltIn (s,ty)) r = 
	  	(BuiltInName (s,ty), [])
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
			val r2 = register (tyInt)
			val (r2',i2) = trans_e f r2
			
			val (iTy,rTy) = (case (getTy r2') of 
								ArrowTy (a,b) => (a,b)
							  | _ => raise Fail "Invalid application")

			val r1 = register (iTy)
			val (r1',i1) = trans_e x r1
			val res' = setTy rTy res
		in
			(res', i1 @ i2 @ [CALL (res', r2', r1')])
		end
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

			val n = name (tyString)

	  		val _ = funs := !funs @ [LIT_STRING (n,s)]
		in
			(r', [ELPTR (r', 1 + size s, "i8", n, 0, 0)])
		end
	  | trans_e (List {exps,...}) r =
			List.foldr (fn (e,(lr,li)) => 
				let
					val (er,ei) = trans_e e (register (tyInt))
					val rr = register (Ast.ListTy (getTy er))
				in
					(rr, li @ ei @ [CONS (rr, er, lr)])
				end) (Null, []) exps
	  | trans_e x res = (register tyInt, [UnconvertedExp x])

	fun emit_r (Reg (i,t)) = "%r" ^ Int.toString i
	  | emit_r (Name (i,t)) = "@anon_" ^ Int.toString i
	  | emit_r (Label i) = "%lab" ^ Int.toString i
	  | emit_r (IntImm i) = Int.toString i
	  | emit_r (BuiltInName (i,t)) = "@" ^ i
	  | emit_r Null = "null"

	fun emit_ty t = if PrettyPrint.ppty t = "string" then "i8*"
	 		   else if PrettyPrint.ppty t = "bool" then "i1"
			   else (case t of 
			    	   ListTy i => "%list_" ^ PrettyPrint.ppty i ^ "*"
			         | _ => "i32")
			   					

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
	  | emit' (CONS (rt,h,t)) =
	  	let
			val listty = emit_ty (getTy rt)

			val szexp = "i32 ptrtoint (" ^ listty ^ "* getelementptr (" ^
						listty ^ "* null, i32 1) to i32)"

			val hptr = register (tyInt)
			val tptr = register (tyInt)
			val rt' = register (tyInt)
		in
	  		emit_r rt' ^ " = call i8* @malloc(" ^ szexp ^ ")" ^ "\n\t" ^
			
			emit_r rt ^ " = bitcast i8* " ^ emit_r rt' ^ " to " ^
				listty ^ "\n\t" ^

			emit_r hptr ^ " = getelementptr " ^ listty ^ " " ^
				emit_r rt ^ ", i32 0, i32 0\n\t" ^

			emit_r tptr ^ " = getelementptr " ^ listty ^ " " ^
				emit_r rt ^	", i32 0, i32 1\n\t" ^

			"store " ^ emit_ty (getTy h) ^ " " ^ emit_r h ^ 
				", " ^ emit_ty (getTy h) ^ "* " ^ emit_r hptr ^ "\n\t" ^
				
			"store " ^ listty ^ " " ^ emit_r t ^ ", " ^
				listty ^ "* " ^ emit_r tptr
		end
	  | emit' _ = "# unemitted"

	fun emit_bd [] = "\n"
	  | emit_bd (h::t) = "\t" ^ emit' h ^ "\n" ^ emit_bd t

	fun emit_builtins () =
		"declare i32 @puts(i8 *)\n" ^
		"declare i8* @malloc(i32)\n"

	fun emit l =
		emit_bd (!funs) ^ 
		"\n\ndefine fastcc i32 @ml_main() {\nentry:\n" ^ emit_bd l ^ "\n\tret i32 0\n}\n\n; built-in forward declarations\n" ^ emit_builtins ()

	fun translate symtab =
		let
			val {venv,tenv,iter_order} = !symtab

			val vkeys = map (fn x => 
							(x, Symtab.lookup_v symtab x)) (!iter_order)
		in
			List.foldl (fn ((s,(t,SOME e)),instr) =>
				let
					val _ = print ("Translating " ^ Symbol.toString s ^ 
								" = " ^ PrettyPrint.ppexp e ^ "\n")

					val forwardSymbol = 
						(case t of NONE => raise Fail ("Translate found unknown symbol")
						         | (SOME (ArrowTy at)) => name(ArrowTy at)
								 | (SOME t) => register t)
									
					val fsL = (case lookup s of
						NONE => 
						(insert s forwardSymbol; 
							forwardSymbol)
					  | SOME t => t)

					val (r,i) = trans_e e fsL

				in
					instr @ i
				end
				| (_,instr) => instr) [] vkeys
		end
end

