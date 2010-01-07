structure ConstFold =
struct

structure A = Ast

fun id a = a

(* a opr b == b opr a *)
fun is_commutative A.Plus = true
  | is_commutative A.Times = true
  | is_commutative A.Equal = true
  | is_commutative A.NEqual = true
  | is_commutative A.BAnd = true
  | is_commutative A.BOr = true
  | is_commutative _ = false (* by default things are not commutative *)

(* (a opr b) opr c == a opr (b opr c) *)
fun is_associative A.Plus = true
  | is_associative A.Times = true
  | is_associative A.Concat = true
  | is_associative A.StrConcat = true
  | is_associative A.BAnd = true
  | is_associative A.BOr = true
  | is_associative _ = false (* by default *)

(* is the rhs an identity *)
fun is_id_func_rhs A.Div _ (A.Int 1) 	= true
  | is_id_func_rhs A.StrConcat _ (A.String "") = true
  | is_id_func_rhs A.Concat _ (A.List {exps=[],...})  = true
  | is_id_func_rhs A.BAnd _ (A.Bool true) = true
  | is_id_func_rhs A.BOr _ (A.Bool false) = true
  | is_id_func_rhs _ _ _ 		= false

(* is the lhs an identity *)
fun is_id_func_lhs A.Plus (A.Int 0) _ 	= true
  | is_id_func_lhs A.Minus (A.Int 0) _ 	= true
  | is_id_func_lhs A.Times (A.Int 1) _ 	= true
  | is_id_func_lhs A.StrConcat (A.String "") _ = true
  | is_id_func_lhs A.Concat (A.List {exps=[],...}) _  = true
  | is_id_func_lhs A.Equal (A.Var {name=sym,...}) _ = (Symbol.toString sym) = "true"
  | is_id_func_lhs A.Equal (A.Bool n) _ = n
  | is_id_func_lhs A.NEqual (A.Bool n) _ = not n
  | is_id_func_lhs _ _ _ 		= false

(* Is this constant *)
fun is_constant (A.Int _) = true
  | is_constant (A.String _) = true
  | is_constant (A.List _) = true
  | is_constant (A.Bool _) = true
  | is_constant _ = false

(* f(f(x)) = f(x) *)
fun is_idempotent A.BAnd = true
  | is_idempotent A.BOr = true
  | is_idempotent A.Mod = true
  | is_idempotent _ = false

(* f(f(x)) = x *)
fun (*is_involution A.UMinus = true   
  | is_involution A.BNot = true 
  | *)is_involution _ = false

(* has no sideeffects? *)
fun is_pure node = true

(* Check for identity functions *)
fun id_func (node as (A.BinOp {attr,opr,lhs,rhs})) = 
	if (is_id_func_lhs opr lhs rhs) then rhs
	else if (is_id_func_rhs opr lhs rhs) then lhs
	else if (is_commutative opr) andalso (is_id_func_lhs opr rhs lhs) then lhs
	else if (is_commutative opr) andalso (is_id_func_rhs opr rhs lhs) then rhs
	else node
  | id_func node = node

(* commute's a node *)
fun commute_node (A.BinOp {attr,opr,lhs,rhs}) = (A.BinOp {attr=attr,opr=opr,lhs=rhs,rhs=lhs})

(* returns true if lhs == rhs *)
fun equivilent_ast lhs rhs = (PrettyPrint.ppexp lhs) = (PrettyPrint.ppexp rhs)

(* Special forms 
 * This is for things like the "Zero property of multiplication"
 * This may be run twice for commutivity
*)
fun special_fold_const (A.BinOp {opr=A.Times,lhs,rhs=A.Int 0,...}) = A.Int 0
  | special_fold_const (A.BinOp {opr=A.BAnd,lhs,rhs=A.Bool false,...}) = A.Bool false
  | special_fold_const (A.BinOp {opr=A.BOr,lhs,rhs=A.Bool true,...}) = A.Bool true
  | special_fold_const node = node

fun special_fold_const' 
	(node as (A.BinOp {opr, ...})) = 
	if is_commutative opr 
	then
		(fn node as (A.BinOp {attr,opr,lhs,rhs}) => 
			let 
				val node' = commute_node node
				val node'' = special_fold_const node'
			in 
				if equivilent_ast node' node'' then node else node''
			end
		 | node => node
		) (special_fold_const node)
	else special_fold_const node
  | special_fold_const' node = node

(* Detect inverse elements *)
fun inverse_element (node as (A.BinOp {opr=A.Div,lhs,rhs,...})) = (* x/x == 1 *)
	if equivilent_ast lhs rhs then (A.Int 1) else node
  | inverse_element (node as (A.BinOp {opr=A.Minus,lhs,rhs,...})) = (* x-x == 0 *)
  	if equivilent_ast lhs rhs then (A.Int 0) else node
  | inverse_element (node as (A.BinOp {opr=A.Equal,lhs,rhs,...})) = (* x = x == true *)
  	if equivilent_ast lhs rhs then (A.Bool true) else node
  | inverse_element (node as (A.BinOp {opr=A.NEqual,lhs,rhs,...})) = (* x <> x == false *)
  	if equivilent_ast lhs rhs then (A.Bool false) else node
  | inverse_element (node as (A.BinOp {opr=A.BAnd,lhs,rhs,...})) = (* x andAlso x == x *)
  	if equivilent_ast lhs rhs then lhs else node
  | inverse_element (node as (A.BinOp {opr=A.BOr,lhs,rhs,...})) = (* x OrElse x == x *)
  	if equivilent_ast lhs rhs then lhs else node
  | inverse_element x = x

(* return true if the nodes should be swapped 
 * we want   App < Var < Int < BinOp
 *
 * This is wrong, we want Int < Var < App < BinOp assuming the tree recurses to the right, so int's are as close to the top as possible
*)
fun compare_bool false true = true
  | compare_bool _ _ = false

fun compare_list [] [] = false
  | compare_list [] (rh::rt) = true
  | compare_list (lh::lt) [] = false
  | compare_list (lh::lt) (rh::rt) = if equivilent_ast lh rh then compare_list lt rt else compare_node lh rh
and compare_node (A.BinOp _) _ = true
  | compare_node _ (A.BinOp _) = false
 (*  ints *)
  | compare_node (A.Int li) (A.Int ri) = li > ri
  | compare_node (A.Int _) _ = true
  | compare_node _ (A.Int _) = false
 (* Bools *)
  | compare_node (A.Bool l) (A.Bool r) = compare_bool l r
  | compare_node (A.Bool _) _ = true
  | compare_node _ (A.Bool _) = false
 (* Lists *)
  | compare_node (A.List {exps=li,...}) (A.List {exps=ri,...}) = compare_list li ri
  | compare_node (A.List _) _ = true
  | compare_node _ (A.List _) = false
 (* variables *)
  | compare_node (A.Var l) (A.Var r) = (Symbol.hash (#name l)) > (Symbol.hash (#name r))
  | compare_node (A.Var _) _ = true
 (* Op *)
  | compare_node (A.Op l) (A.Op r) = (Symbol.hash (#symbol l)) > (Symbol.hash (#symbol r))
  | compare_node (A.Op _) _ = true
  | compare_node _ (A.Op _) = false
 (* Application -- TODO: Make sure we compare the function we're applying not just it's arguments*)
  | compare_node (A.App {exps=lexps,...}) (A.App {exps=rexps,...}) = List.exists (fn (a,b) => compare_node a b ) (ListPair.zip (lexps,rexps))
 (* Failure *)
  | compare_node lhs rhs = raise Fail ("Unknown comparison: " ^ (PrettyPrint.ppexp lhs) ^ " > " ^ (PrettyPrint.ppexp rhs))

(* Constant Folding *)
fun fold_const (A.BinOp {opr=A.Plus,  lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Int (lhs+rhs)
  | fold_const (A.BinOp {opr=A.Minus, lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Int (lhs-rhs)
  | fold_const (A.BinOp {opr=A.Times, lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Int (lhs*rhs)
  | fold_const (A.BinOp {opr=A.Div,   lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Int (lhs div rhs)
  | fold_const (A.BinOp {opr=A.StrConcat,lhs=A.String lhs, rhs=A.String rhs,...}) = A.String (lhs^rhs)
  (* this should know about equality types *)
  | fold_const (A.BinOp {opr=A.Equal, lhs=A.Bool lhs, rhs=A.Bool rhs,...}) = A.Bool (lhs=rhs)
  | fold_const (A.BinOp {opr=A.Equal, lhs=A.String lhs, rhs=A.String rhs,...}) = A.Bool (lhs=rhs)
  | fold_const (A.BinOp {opr=A.Equal, lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Bool (lhs=rhs)
  | fold_const (A.BinOp {opr=A.NEqual, lhs=A.Bool lhs, rhs=A.Bool rhs,...}) = A.Bool (lhs<>rhs)
  | fold_const (A.BinOp {opr=A.NEqual, lhs=A.String lhs, rhs=A.String rhs,...}) = A.Bool (lhs<>rhs)
  | fold_const (A.BinOp {opr=A.NEqual, lhs=A.Int lhs, rhs=A.Int rhs,...}) = A.Bool (lhs<>rhs)
  | fold_const node = node

(* Reorder tree *)
fun comm_reorder_tree (node as (A.BinOp {attr, opr, lhs, rhs})) = 
	if is_commutative opr andalso compare_node lhs rhs then commute_node node else node
  | comm_reorder_tree node = node

(*
(* (opr a (opr b c)) => (opr (opr a b) (opr c) *)
(* FIXME: Figure out attrs *)
fun rotate_left (node as (A.BinOp {attr, opr=opra, lhs, rhs=(A.BinOp {attr=rattr, opr=oprb, lhs=rlhs, rhs=rrhs})}))
	= if opra = oprb then (A.BinOp {attr=rattr, opr=opra, lhs=fold_const (A.BinOp {attr=attr, opr=opra, lhs=lhs, rhs=rlhs}), rhs=rrhs}) else node
  | rotate_left _ = raise Fail "Can't Happen"

(* (opr (opr a b) c) => (opr a (opr b c))        right *)
fun rotate_right (node as (A.BinOp {attr, opr=opra, lhs=(A.BinOp {attr=lattr, opr=oprb, lhs=llhs, rhs=lrhs}), rhs}))
	= if opra = oprb then (A.BinOp {attr=lattr, opr=opra, lhs=llhs, rhs=fold_const (A.BinOp {attr=attr, opr=opra, lhs=lrhs, rhs=rhs})}) else node
  | rotate_right _ = raise Fail "Can't Happen"

(* (opr a (opr b c)) => (opr (opr a b) (opr c)   left
 *   if is_constant a and is_constant b
 *   if a>b and is_associative opr and is_commutative opr
 *   if is_constant c
 * (opr (opr a b) c) => (opr a (opr b c))        right
 *   if is_constant b and is_constant c
 *   if b>c and is_associative opr and is_commutative opr
 *   if is_constant a
 *)

fun is_rotate_left (node as (A.BinOp {attr, opr=opra, lhs, rhs=(A.BinOp {attr=rattr, opr=oprb, lhs=rlhs, rhs=rrhs})}))
  	= if opra = oprb andalso is_associative opra then
		if is_constant lhs andalso is_constant rlhs then  true
		else if compare_node lhs rlhs andalso is_commutative opra then true
		else if is_constant rrhs then true
		else false
	else false

fun is_rotate_right (node as (A.BinOp {attr, opr=opra, lhs=(A.BinOp {attr=lattr, opr=oprb, lhs=llhs, rhs=lrhs}), rhs}))
  	= if opra = oprb andalso is_associative opra then
		if is_constant lrhs andalso is_constant lrhs then true
		else if compare_node lrhs rhs andalso is_commutative opra then true
		else if is_constant llhs then true
		else false
	else false

fun assoc_reorder_tree (node as (A.BinOp {attr, opr=opra, lhs, rhs=(A.BinOp {attr=rattr, opr=oprb, lhs=rlhs, rhs=rrhs})}))
	= if is_rotate_left node then (rotate_left node) else node
  | assoc_reorder_tree (node as (A.BinOp {attr, opr=opra, lhs=(A.BinOp {attr=lattr, opr=oprb, lhs=llhs, rhs=lrhs}), rhs}))
  	= if is_rotate_right node then (rotate_right node) else node
  | assoc_reorder_tree node = node
*)

fun opt_associativity (node as (A.BinOp {attr, opr=opra, lhs, rhs=(A.BinOp {attr=rattr, opr=oprb, lhs=rlhs, rhs=rrhs})}))
	= if opra = oprb andalso is_associative opra then
		A.App {attr=[], exps=[
			A.Var {attr=[], name=(Symbol.fromString "foldany"), symtab=ref (Symtab.symtab Symtab.top_level)},
			A.Op {symbol=AstOps.opr_to_symbol opra,symtab=Symtab.top_level,attr=[]},
			A.List {attr=[], exps=[lhs,rlhs,rrhs]}]}
	else
		node
  | opt_associativity (node as (A.BinOp {attr, opr=opra, lhs=(A.BinOp {attr=lattr, opr=oprb, lhs=llhs, rhs=lrhs}), rhs}))
	= if opra = oprb andalso is_associative opra then
		A.App {attr=[], exps=[
			A.Var {attr=[], name=(Symbol.fromString "foldany"), symtab=ref (Symtab.symtab Symtab.top_level)},
			A.Op {symbol=AstOps.opr_to_symbol opra,symtab=Symtab.top_level,attr=[]},
			A.List {attr=[], exps=[llhs,llhs,rhs]}]}
	else
		node
  | opt_associativity node = node

(* Helper debug function *)
fun debugDump name f x = 
	let 
		val x' = f x
	in
		if equivilent_ast x x' then 
			x'
		else
		let
			val _ = print (name ^ ": " ^ (PrettyPrint.ppexp x) ^ " => " ^ (PrettyPrint.ppexp x')^"\n")
		in 
			x'
		end
	end

(* optimisations to apply *)
fun expfun node = (
	  (debugDump "id_func" id_func)
	o (debugDump "special_fold_const" special_fold_const')
	o (debugDump "inverse element" inverse_element)
	o (debugDump "fold_const1" fold_const)
(*        o (debugDump "assoc_reorder_tree" assoc_reorder_tree) *)
	o (debugDump "fold_const2" fold_const)
	o (debugDump "comm_reorder_tree" comm_reorder_tree)
	) node

fun optConstFold symtab = (AstOps.ast_map_symtab {
	decfun = id,
	expfun = expfun,
	patfun = id,
	bindfun = id,
	tyfun = id,
	oprfun = id,
	clausesfun = id,
	clausefun = id
} symtab; ())

end
