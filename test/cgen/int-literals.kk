// Integer construction and patterns agree at the small, 32-bit and 64-bit boundaries.
noinline fun classify(x : int) : string
  match(x) {
    -9223372036854775809 -> "case 0"
    -9223372036854775808 -> "case 1"
    -9223372036854775807 -> "case 2"
    -2147483648 -> "case 3"
    -2147483647 -> "case 4"
    -8192 -> "case 5"
    -8191 -> "case 6"
    8191 -> "case 7"
    8192 -> "case 8"
    2147483647 -> "case 9"
    2147483648 -> "case 10"
    9223372036854775807 -> "case 11"
    9223372036854775808 -> "case 12"
    _ -> "other"
  }

fun main()
  [-9223372036854775809, -9223372036854775808, -9223372036854775807,
   -2147483648, -2147483647, -8192, -8191, 8191, 8192,
   2147483647, 2147483648, 9223372036854775807, 9223372036854775808, 42].foreach fn(x)
    x.println
    classify(x).println
