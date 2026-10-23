import std/num/int32

// A raw field is read from the block of its box. A read after the box is dropped or reused
// (here after the recursive calls, which follow the drop) must read a copy taken before.
type tree
  Leaf
  Node(left : tree, key : int32, right : tree)

fun sum(t : tree) : int32
  match t
    Leaf -> 0.int32
    Node(l,k,r) -> sum(l) + k + sum(r)

fun incr(t : tree) : tree
  match t
    Leaf -> Leaf
    Node(l,k,r) ->
      val l' = incr(l)
      Node(l', k + 1.int32, incr(r))

noinline fun make(n : int) : div tree
  if n <= 0 then Leaf else Node(make(n - 1), n.int32, make(n - 2))

fun main()
  val t = make(6)
  println(sum(t).show)
  println(sum(incr(t)).show)
  println(sum(t).show)
  println(sum(incr(make(6))).show)
