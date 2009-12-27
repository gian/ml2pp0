structure ConstFold = 
struct 
open TypedAST


fun constFold (Node ((BinOp Plus, _),[Leaf (Integer lhs,_), Leaf (Integer rhs,_)]) ) = Node ((Integer (lhs+rhs),TyName "int"), [])
  | constFold (Node ((BinOp Minus, _),[Leaf (Integer lhs,_), Leaf (Integer rhs,_)]) ) = Node ((Integer (lhs-rhs),TyName "int"), [])
  | constFold (Node ((BinOp Times, _),[Leaf (Integer lhs,_), Leaf (Integer rhs,_)]) ) = Node ((Integer (lhs*rhs),TyName "int"), [])
  | constFold (n as Node ((BinOp Divide, _),[Leaf (Integer lhs,_), Leaf (Integer rhs,_)]) ) = if rhs <> 0 then Node ((Integer (lhs div rhs),TyName "int"), []) else n
  | constFold n = n

fun mapAst f (Leaf a) = f (Leaf a)
  | mapAst f (Node (a, ch)) = f (Node (a, map (mapAst f) ch))

fun mapForest f forest = map (mapAst f) forest

fun optConstFold tast = mapForest constFold tast




end
