structure CodeGen =
struct
	open Intermediate
	open Ast

	val sep = ", "
	val eql = " = "

	fun c l = String.concat l

	fun e_ty IntTy = "i32"
	  | e_ty BoolTy = "i1"
	  | e_ty WordTy = "i32"
	  | e_ty CharTy = "i8"
	  | e_ty (TupleTy l) = c ["{ ", 
	  						  String.concatWith sep (map e_ty l),
							  " }"]
	  | e_ty t = c ["<<<<UNKNOWN TY: ",
	  				PrettyPrint.ppty t,
					">>>>"]


	fun e_st' (Reg (s,t)) = c ["%", Symbol.toString s]
	  | e_st' (Name (s,t)) = c ["@", Symbol.toString s]
	  | e_st' (Ptr (s,t)) = c ["%", Symbol.toString s]
	  | e_st' (IntImm v) = Int.toString v
	  | e_st' (WordImm v) = Word32.toString v
	  | e_st' (CharImm v) = Int.toString (Char.ord v)
	  | e_st' (BoolImm v) = if v then "1" else "0"
	  | e_st' (Label i) = c ["L", Int.toString i]
	  | e_st' (BuiltInName (s,t)) = c ["@", s]
	  | e_st' (Undef) = "undef"
	  | e_st' (Composite l) = c ["{ ", 
	  							String.concatWith sep (map e_st' l),
								" }"]
	  | e_st' _ = "<<<<<UNKNOWN STORE>>>>>"


	fun e_st (Reg (s,t)) = c [e_ty t, " %", Symbol.toString s]
	  | e_st (Name (s,t)) = c ["@", Symbol.toString s]
	  | e_st (Ptr (s,t)) = c [e_ty t, "* %", Symbol.toString s]
	  | e_st (IntImm v) = c ["i32 ", Int.toString v]
	  | e_st (WordImm v) = c ["i32 ", Word32.toString v]
	  | e_st (CharImm v) = c ["i8 ", Int.toString (Char.ord v)]
	  | e_st (BoolImm v) = c ["i1 ", if v then "1" else "0"]
	  | e_st (Label i) = c ["L", Int.toString i]
	  | e_st (BuiltInName (s,t)) = c ["@", s]
	  | e_st (Undef) = "undef"
	  | e_st (Composite l) = c ["{ ", 
	  							String.concatWith sep (map e_st l),
								" }"]
	  | e_st _ = "<<<<<UNKNOWN STORE>>>>>"

	fun e_as t ins = c
		[e_st' t,
		 eql,
		 ins, " ",
		 e_ty (getTy t),
		 " "]

	fun e_op n (x,y,z) = c
		[e_as x n,
		 e_st' y,
		 sep,
		 e_st' z]
	
	fun e_ir (ADD r) = e_op "add" r
	  | e_ir (ALLOCA (s,t)) = c 
	  	[e_st' s,
		 eql,
		 "alloca ",
		 e_ty t]
	  | e_ir (AND r) = e_op "and" r
	  | e_ir (BR i) = c
	  	["br label %L",
		 Int.toString i]
	  | e_ir (CALL (x,y,z)) = c
	  	[e_st' x,
		 eql,
		 "call ",
		 "fastcc ",
		 e_ty (getTy x), " ",
		 e_st' y,
		 "(",
		 e_st z,
		 ")"]
	  | e_ir (CBR (i,trl,fal)) = c
	    ["br ",
		 e_st i,
		 sep,
		 "label %L",
		 Int.toString trl,
		 sep,
		 "label %L",
		 Int.toString fal]
	  | e_ir (CONS r) = ";<<<CONS>>>>"
	  | e_ir (DIV r) = e_op "sdiv" r
	  | e_ir (ELPTR r) = ";<<<ELPTR>>>"
	  | e_ir (ICMP (x,opr,y,z)) = c
	  	[e_st' x,
		 eql,
		 "icmp ",
		 opr," ",
		 e_st y,
		 sep,
		 e_st' z]
	  | e_ir (MUL r) = e_op "mul" r
	  | e_ir (RET (t,s)) = c
	  	["ret ",
		 e_st s]
	  | e_ir (SUB r) = e_op "sub" r
	  | e_ir (STORE (s1,s2)) = c
	  	["store ",
		 e_st s2,
		 sep,
		 e_st s1]
	  | e_ir (LOAD (s1,s2)) = c
	  	[e_st' s1,
		 eql,
		 "load ",
		 e_st s2]
	  | e_ir (MOV (s1,s2)) = e_op "or" (s1,IntImm 0,s2)
	  | e_ir (FUNCTION (n,t2,[inp],body)) = c
	  	["define ",
		 e_ty t2,
		 " ",
		 e_st' n,
		 "( ",
		 e_st inp,
		 " ) {\n",
		 String.concatWith "\n\t" (map e_ir body),
		 "\n}\n"]
	  | e_ir (LABEL l) = c
	  	["L",
		 Int.toString l,
		 ": "]
      | e_ir (PHI (r,t,(b1,l1),(b2,l2))) = c
	  	[e_st' r,
		 eql,
		 "phi ",
		 e_ty t,
		 " [ ",
		 e_st' b1,
		 sep,
		 "%L",
		 Int.toString l1,
		 " ]",
		 sep,
		 " [ ",
		 e_st' b2,
		 sep,
		 "%L",
		 Int.toString l2,
		 " ]"]
	  | e_ir (EXTRACT (a,t,b,i)) = c
	  	[e_st' a,
		 eql,
		 "extractvalue ",
		 e_ty t, " ",
		 e_st' b,
		 sep,
		 Int.toString i]
	  | e_ir (INSERT (a,t,b,d,i)) = c 
	  	[e_st' a,
		 eql,
		 "insertvalue ",
		 e_ty t, " ",
		 e_st' b,
		 sep,
		 e_st d,
		 sep,
		 Int.toString i]
	  | e_ir (UnconvertedExp e) = "; Unconverted: " ^ PrettyPrint.ppexp e
	  | e_ir _ = ";<<<<UNIMPLEMENTED>>>>"


	fun codegen (funs, irl) = c
		[String.concatWith "\n\n" (map e_ir funs),
		 "\n\ndefine i32 @main() {\nentry:\n\t",
		 (String.concatWith "\n\t" (map e_ir irl)),
		 "\n\tret i32 0\n}\n"]
end

