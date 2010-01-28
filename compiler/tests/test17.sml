
fun foo x = hd x

fun bar x = tl x

val a = tl [1, 2, 3, 4]

val b = tl [1, 2, 3, 4, 5]

val good = foo [1,2]

val bad = foo []

val bad2 = tl (tl (tl (tl [1])))

val bad3 = hd bad2
