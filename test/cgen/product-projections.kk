// Branches may read one product component without ever binding its sibling.
// Both references must still be consumed, including when a closure captures one.
type fields
  Fields(left : list<int>, right : list<int>)

noinline fun choose(p : fields, first : bool) : list<int>
  match p
    Fields(xs, ys) -> if first then xs else ys

noinline fun capture(p : fields, first : bool) : (() -> list<int>)
  match p
    Fields(xs, ys) -> if first then (fn() xs) else (fn() ys)

fun main()
  println(choose(Fields([1,2], [3,4]), True))
  println(choose(Fields([1,2], [3,4]), False))
  val f = capture(Fields([5,6], [7,8]), True)
  println(f())
  println(f())
  println(capture(Fields([5,6], [7,8]), False)())
  println([1].init)
  println([1,2,3].init)
