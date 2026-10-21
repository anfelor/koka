import std/num/int32
import std/num/int64

// Scalar reads must survive resetting their owner, for both immediate int32
// values and heap-backed int64 values. Shared inputs also exercise allocation
// instead of reuse; the generic mapper must retain non-scalar fields normally.
type tree<a>
  Leaf
  Node(left : tree<a>, value : a, right : tree<a>)

fun tmap(t : tree<a>, f : a -> e b) : e tree<b>
  match t
    Leaf -> Leaf
    Node(l,x,r) -> Node(tmap(l,f), f(x), tmap(r,f))

fun values(t : tree<a>) : list<a>
  match t
    Leaf -> []
    Node(l,x,r) -> values(l) ++ [x] ++ values(r)

noinline fun make(x : a) : tree<a>
  Node(Node(Leaf,x,Leaf),x,Node(Leaf,x,Leaf))

fun main()
  val small = make(41.int32)
  println(tmap(small, fn(x) x.inc).values.map(fn(x) x.show))
  println(small.values.map(fn(x) x.show))
  println(tmap(make(41.int32), fn(x) x.inc).values.map(fn(x) x.show))
  val big = make(0x7FFF_FFFF_FFFF_FFFE.int64)
  println(tmap(big, fn(x) x.inc).values.map(fn(x) x.show))
  println(big.values.map(fn(x) x.show))
  println(tmap(make(0x7FFF_FFFF_FFFF_FFFE.int64), fn(x) x.inc).values.map(fn(x) x.show))
  val strings = make("field".repeat(3))
  println(tmap(strings, fn(x) x ++ "!").values)
  println(strings.values)
