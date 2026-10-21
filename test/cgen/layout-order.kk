// Pointer fields must precede enum bytes, including after match partitioning.
type color { Red; Black }
type tree {
  Leaf
  Node(color: color, left: tree, key: int, value: bool, right: tree)
}
fun insert(t: tree, k: int): tree {
  match t {
    Leaf -> Node(Red, Leaf, k, True, Leaf)
    Node(c,l,x,v,r) -> if k < x then Node(c,insert(l,k),x,v,r)
                      else Node(Black,l,x,v,insert(r,k))
  }
}
fun build(n: int, t: tree): div tree {
  if n <= 0 then t else build(n - 1, insert(t,n))
}
fun total(t: tree): int {
  match t {
    Leaf -> 0
    Node(_,l,k,_,r) -> total(l) + k + total(r)
  }
}
fun main() {
  val t = build(30,Leaf)
  println(total(t))
  println(total(t))
}
