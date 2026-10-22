// Aggregate fields must survive releasing their heap owner. Captures create a
// new storage scope; nested reads and branch results retain independent values.
value struct payload(left: string, right: string)
reference struct holder(contents: payload, spare: string)
reference struct outer(inner: holder, tag: string)

noinline fun make(s: string): holder {
  Holder(Payload(s ++ "-left",s ++ "-right"),s ++ "-spare")
}
noinline fun take-payload(h: holder): payload {
  match h { Holder(p,_) -> p }
}
noinline fun capture(h: holder): (() -> string) {
  match h { Holder(p,_) -> fn() { p.left ++ p.right } }
}
noinline fun choose(h: holder, b: bool): payload {
  match h { Holder(p,s) -> if b then p else Payload(s,p.left) }
}
noinline fun nested(o: outer): (() -> string) {
  capture(o.inner)
}
fun main() {
  val f = capture(make("a"))
  println(f())
  println(f())
  val p = take-payload(make("b"))
  println(p.left ++ p.right)
  val q = choose(make("c"),False)
  println(q.left ++ q.right)
  val g = nested(Outer(make("d"),"tag"))
  println(g())
}
