fun fib 0 = 0 
  | fib 1 = 1
  | fib 2 = 1
  | fib n = fib(n-2) + fib(n-1)
 
val k = input_int 0

val j = fib k

val l = print_int j