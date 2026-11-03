// Sibling constructors precede their nested tests. Wildcard rows must undergo
// the same column permutation; guarded alternatives retain source-row order.
type tree<a>
  Leaf
  Node(value : a, left : tree<a>, right : tree<a>)

noinline fun guard(n : int) : bool
  n > 0

noinline fun classify(t : tree<int>) : int
  match t
    Node(0, Node(x,_,_), Node(y,_,_)) | guard(x) -> x + y
                                    | x == 0 -> 10 + y
    Node(_, Leaf, Node(y,_,_)) -> 100 + y
    Node(_, Node(x,_,_), _) | guard(x) -> 200 + x
    Node(_, _, Node(y,_,_)) -> 300 + y
    _ -> 400

// Unit enum fields exercise grouped predicates after both child tags hold.
noinline fun grouped(t : tree<bool>) : bool
  match t
    Node(False, Node(True,_,_), Node(True,_,_)) -> True
    _ -> False

// Pending columns keep their type parameters when fields are appended.
noinline fun shape(t : tree<a>) : int
  match t
    Node(_, Node(_,_,_), Node(_,_,_)) -> 1
    Node(_, Leaf, _) -> 2
    _ -> 3

fun main()
  val leaf = Leaf
  val pos = Node(1,leaf,leaf)
  val neg = Node(-1,leaf,leaf)
  [Leaf, Node(0,pos,pos), Node(0,neg,pos), Node(0,pos,leaf),
   Node(0,leaf,pos), Node(0,leaf,leaf), Node(2,neg,pos),
   Node(0,Node(0,leaf,leaf),pos)].foreach fn(t)
    println(classify(t))
  println(shape(Node(0,pos,pos)))
  println(shape(Node(True,Leaf,Node(False,Leaf,Leaf))))
  println(shape(Node("x",Node("y",Leaf,Leaf),Leaf)))
  var hits := 0
  [False,True].foreach fn(c)
    [Leaf,Node(False,Leaf,Leaf),Node(True,Leaf,Leaf)].foreach fn(l)
      [Leaf,Node(False,Leaf,Leaf),Node(True,Leaf,Leaf)].foreach fn(r)
        if grouped(Node(c,l,r)) then hits := hits + 1
  println(hits)
