structure ConstFold = 
struct 
open TypedAST
open Debug


fun constFold (Node ((BinOp Plus, _),[Leaf (Integer lhs,_), Leaf (Integer rhs,_)]) ) = Leaf ((Integer (lhs+rhs),TyName "int"))
  | constFold (Node ((BinOp Minus, _),[Leaf (Integer lhs,_), Leaf (Integer rhs,_)]) ) = Leaf ((Integer (lhs-rhs),TyName "int"))
  | constFold (Node ((BinOp Times, _),[Leaf (Integer lhs,_), Leaf (Integer rhs,_)]) ) = Leaf ((Integer (lhs*rhs),TyName "int"))
  | constFold (n as Node ((BinOp Divide, _),[Leaf (Integer lhs,_), Leaf (Integer rhs,_)]) ) = if rhs <> 0 then Leaf ((Integer (lhs div rhs),TyName "int")) else n
 (* Identity Functions *) 
  | constFold (Node ((BinOp Plus, _),[Leaf (Integer 0,_), rhs]) ) = rhs
  | constFold (Node ((BinOp Minus, _),[Leaf (Integer 0,_), rhs]) ) = rhs
  | constFold (Node ((BinOp Times, _),[Leaf (Integer 1,_), rhs]) ) = rhs
  | constFold (Node ((BinOp Plus, _),[lhs, Leaf (Integer 0,_)]) ) = lhs
  | constFold (Node ((BinOp Minus, _),[lhs, Leaf (Integer 0,_)]) ) = lhs
  | constFold (Node ((BinOp Times, _),[lhs, Leaf (Integer 1,_)]) ) = lhs
  | constFold (Node ((BinOp Divide, _),[lhs, Leaf (Integer 1,_)]) ) = lhs
 (* multiplication by zero *)
  | constFold (Node ((BinOp Times, _),[Leaf (Integer 0,_), rhs]) ) = Leaf ((Integer 0, TyName "int"))
  | constFold (Node ((BinOp Times, _),[lhs, Leaf (Integer 0,_)]) ) = Leaf ((Integer 0, TyName "int"))
 (* assertions *)
  | constFold (n as (Node (_,[]))) = raise Fail "Node without children"
 (* no optimisation *)
  | constFold n = n

fun mapAst f (Leaf a) = f (Leaf a)
  | mapAst f (Node (a, ch)) = f (Node (a, map (mapAst f) ch))

fun mapForest f forest = map (mapAst f) forest

fun debugTransform xfrm node = 
	let 
		val result = xfrm node 
	in 
		if node <> result then
			Debug.print_dbg ((pptypedast_h node) ^ " => " ^ (pptypedast_h result) ^ "\n")
		else
			();
		result
	end
	

fun optConstFold tast = mapForest (debugTransform constFold)  tast

end
