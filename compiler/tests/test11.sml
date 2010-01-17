fun f x = if x < 100 then x*50 else x*500

fun g x = x + (print_int (f (input_int 0)))

val p = g 0

