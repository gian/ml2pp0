structure CVC3 =
struct
	val plusExpr = _import "cvc_plusExpr" public: int ref * int ref -> int ref;

	val nullExpr = _import "cvc_nullExpr" public: unit -> int ref;
end
