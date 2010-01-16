fun f n = if n = [] then 0 else hd n + f (tl n)


val k = [1, 2, 3, 4, 5]

val m = f k


