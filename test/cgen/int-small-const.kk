// Constant arithmetic must preserve big integers and small-integer overflow.
noinline fun add-right(x : int) : int { x + 1 }
noinline fun add-left(x : int) : int { 1 + x }
noinline fun sub-right(x : int) : int { x - 1 }
noinline fun sub-negative(x : int) : int { x - (-1) }
noinline fun sub-left(x : int) : int { 1 - x }
noinline fun add-upper(x : int) : int { x + 8191 }
noinline fun add-lower(x : int) : int { x + (-8192) }
noinline fun add-outside(x : int) : int { x + 8192 }
noinline fun sub-outside(x : int) : int { x - (-8192) }

fun main()
  [0, -10, 2305843009213693951, -2305843009213693952,
   10000000000000000000000000000000000000000].foreach fn(x)
    add-right(x).println
    add-left(x).println
    sub-right(x).println
    sub-negative(x).println
    sub-left(x).println
    add-upper(x).println
    add-lower(x).println
    add-outside(x).println
    sub-outside(x).println
