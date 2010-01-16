structure Intermediate =
struct
	open Ast
	open Types

	type symbol = Symbol.symbol

	datatype store = Reg of symbol * Ast.ty
	               | Name of symbol * Ast.ty
				   | IntImm of int
				   | WordImm of Word32.word 
				   | CharImm of char
				   | BoolImm of bool
				   | Label of int
				   | BuiltInName of string * Ast.ty
				   | Composite of store list
				   | Ptr of symbol * Ast.ty
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

	fun unique_register (ty) = Reg ((rc := !rc + 1; 
							Symbol.fromString ("_r" ^ 
										Int.toString (!rc))), ty)
	fun unique_name (ty) = Name ((nc := !nc + 1; 
							Symbol.fromString ("_anon_" ^ 
										Int.toString (!nc))), ty)
	fun name (s,t) = Name (s,t)
	fun register (s,t) = Reg (s,t)
	fun label () = (lc := !lc + 1; !lc)
	fun ptr (s,t) = Ptr (s,t)

	fun setTy t (Reg (d,_)) = Reg (d, t)
	  | setTy t _ = raise Fail "setTy called on non-register"

	fun getTy (Reg (_,t)) = t
	  | getTy (BuiltInName (s,t)) = t
	  | getTy (Name (i,t)) = t 
	  | getTy (Label i) = raise Fail "getTy called on Label"
	  | getTy (IntImm i) = raise Fail "getTy called on IntImm"

	datatype ir =
		ADD of store * store * store
	  | ALLOCA of store * Ast.ty 
	  |	AND of store * store * store 
	  | BR of int
	  | CALL of store * store * store
	  | CBR of store * int * int
	  | CONS of store * store * store
	  | DIV of store * store * store
	  | ELPTR of store * int * string * store * int * int
	  | FUNCTION of store * Ast.ty * store list * ir list
	  | ICMP of store * string * store * store 
	  |	LABEL of int 
	  | LIT_INT of int
	  | LIT_STRING of store * string
	  | LOAD of store * store
	  |	MUL of store * store * store
	  |	MOV of store * store
	  | PHI of store * Ast.ty * (store * int) * (store * int)
	  | RET of Ast.ty * store
	  |	SUB of store * store * store
	  |	SUBI of store * store * int
	  | STORE of store * store
	  | UnconvertedExp of Ast.ast

	fun trans_e (Node (Var s,SOME t,st,_)) =
		(case lookup s of
					SOME (Ptr (ps,pt)) => 
					let
						val dr = unique_register pt
					in
						(dr, [LOAD (dr,Ptr (ps,pt))])
					end
				  | SOME x => (x,[])
			  	  | NONE =>
				  let
				  	val r = (case t of
						ArrowTy (t1,t2) => name (s, t)
				      | x => register (s,t))
					val _ = insert s r
				  in
			  			(r,[])
			  	  end)
	  | trans_e (Node (VarPat s,SOME t,st,_)) =
		let
			val store = (case lookup s of
					SOME x => x
			  	  | NONE =>
				  let
				  	val r = (case t of
						ArrowTy (t1,t2) => name (s, t)
				      | x => register (s,t))
					val _ = insert s r
				  in
			  			r
			  	  end)
		in
			(store,[])
		end
	  | trans_e (Node (Int i, _, _, _)) =
	  		(IntImm i, [])
	  | trans_e (Node (Word i, _, _, _)) =
	  		(WordImm i, [])
	  | trans_e (Node (Char i, _, _, _)) =
	  		(CharImm i, [])
	  | trans_e (Node (Seq, SOME rt, _, ch)) =
	  	let
			val is = map trans_e ch

			fun grp l [] = []
			  | grp l [(r,ins)] = [LABEL l] @ ins @ [RET (rt, r)]
			  | grp l ((r,ins)::t) =
			  	let
					val lab = label ()
				in
					[LABEL l] @ ins @ [BR lab] @ grp lab t
				end

			val start = label ()
		in
			(Label start, grp start is)
		end
	  | trans_e (Node (Let _,_,_,_)) = 
	  		raise Fail "[BUG] CodeGen encountered Let"
	  | trans_e (Node (App, SOME rt, _, [tm1,tm2])) =
		(case tm1 of 
			Node (BuiltIn (s,t),_,_,_) => trans_builtin (s,t) tm2
          | _ =>let
		  			val _ = print ("Not BuiltIn!")
		  			val ret = unique_register rt 
					val (s2,ins2) = trans_e tm2
					val (s1,ins1) = trans_e tm1
				in
					(ret,
					ins2 @
					ins1 @
					[CALL (ret,s1,s2)])
				end)
	  | trans_e (Node (Tuple, SOME t, _, ch)) =
	  	let
			val comb = map trans_e ch
			val (ts,is) = ListPair.unzip comb
			val c = Composite ts
			val is = List.foldl (fn (a,b) => b @ a) [] is
		in
			(c, is)
		end
	  | trans_e n = (Label 0, [UnconvertedExp n])
	
	and trans_builtin' ("+",ArrowTy(_,rt)) (Composite [t1,t2]) =
		(fn r => (r, [ADD (r,t1,t2)])) (unique_register rt)
	  | trans_builtin' ("-",ArrowTy(_,rt)) (Composite [t1,t2]) =
		(fn r => (r, [SUB (r,t1,t2)])) (unique_register rt)
	  | trans_builtin' ("*",ArrowTy(_,rt)) (Composite [t1,t2]) =
		(fn r => (r, [MUL (r,t1,t2)])) (unique_register rt)
	  | trans_builtin' ("div",ArrowTy(_,rt)) (Composite [t1,t2]) =
		(fn r => (r, [DIV (r,t1,t2)])) (unique_register rt)
	  | trans_builtin' ("=",ArrowTy(_,rt)) (Composite [t1,t2]) =
		(fn r => (r, [ICMP (r,"eq",t1,t2)])) (unique_register rt)
	  | trans_builtin' ("<=",ArrowTy(_,rt)) (Composite [t1,t2]) =
		(fn r => (r, [ICMP (r,"sle",t1,t2)])) (unique_register rt)
	  | trans_builtin' (">=",ArrowTy(_,rt)) (Composite [t1,t2]) =
		(fn r => (r, [ICMP (r,"sge",t1,t2)])) (unique_register rt)
	  | trans_builtin' ("<",ArrowTy(_,rt)) (Composite [t1,t2]) =
		(fn r => (r, [ICMP (r,"lt",t1,t2)])) (unique_register rt)
	  | trans_builtin' (">",ArrowTy(_,rt)) (Composite [t1,t2]) =
		(fn r => (r, [ICMP (r,"gt",t1,t2)])) (unique_register rt)
	  | trans_builtin' ("<>",ArrowTy(_,rt)) (Composite [t1,t2]) =
		(fn r => (r, [ICMP (r,"ne",t1,t2)])) (unique_register rt)
	  | trans_builtin' _ _ = raise Fail "Unhandled builtin"

	and trans_builtin b tm2 =
		let
			val (tm2',ins2) = trans_e tm2
			val (tm1',ins1) = trans_builtin' b tm2'
		in
			(tm1',
			 ins2 @
			 ins1)
		end
	fun translate symtab =
		let
			val {venv,tenv,iter_order} = !symtab

			val vkeys = map (fn x => 
							(x, Symtab.lookup_v symtab x)) (!iter_order)
		in
			List.foldl (fn ((s,(SOME t,SOME e)),instr) =>
				let
					val _ = print ("Translating " ^ Symbol.toString s ^ 
								" = " ^ PrettyPrint.ppexp e ^ "\n")

					val (r,i) = trans_e e

					val strins = 
						(case lookup s of
							SOME x => [STORE (x,r)]
						  | NONE =>
						  	let
								val s' = ptr (s,t)
								val _ = insert s s'
							in
								[ALLOCA (s',t),
								 STORE (s',r)]
							end)

				in
					instr @ i @ strins
				end
				| (_,instr) => instr) [] vkeys
		end
end

