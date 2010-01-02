(* Test program 1 *)

(* Operators - taken from http://mlton.org/OperatorPrecedence *)
infix 7 * / mod div
infix 6 + - ^
infixr 5 :: @
infix 4 = <> > >= < <=
infix 3 := o
infix 0 before

val a : int = 123 + 345

fun f 0 = 11
  | f x = x * x + 10
and g x = x + x

val p = fn x => x + 1

val myString' = "hello, world"

fun testF x = 
	let
		val p = x * x
	in
		p
	end

type k = int * int * string

type r = {hello : string, foo : int, bar : real}



