// Sparse boxed matches keep a single default, including guard failures and
// defaults that return the original value. Exercise tags before and after it.
type item
  Empty
  First(n : int)
  Second(n : int)
  Text(s : string)
  Nested(x : item)
  Last

noinline fun score(x : item) : int
  match x
    Second(n) | n > 0 -> n
    Text(s) -> s.count
    _ -> -1

noinline fun replace-text(x : item) : item
  match x
    Text(_) -> Last
    _ -> x

fun main()
  [Empty, First(1), Second(2), Second(-2), Text("hello"), Nested(Second(3)), Last].foreach fn(x)
    println(score(x))
    println(score(replace-text(x)))
