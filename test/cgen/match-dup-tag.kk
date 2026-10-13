// A match on the later constructors of a type, whose scrutinee is first duplicated
// (as for a borrowed binder): the tag test must keep the constructor offset.
type expr
  Var( : int )
  Val( : int )
  Add( l : expr, r : expr )
  Mul( l : expr, r : expr )

fun append-add( e0 : expr, e3 : expr ) : expr
  match e0
    Add(e1,e2) -> Add(e1, append-add(e2,e3))
    _          -> Add(e0,e3)

fun append-mul( e0 : expr, e3 : expr ) : expr
  match e0
    Mul(e1,e2) -> Mul(e1, append-mul(e2,e3))
    _          -> Mul(e0,e3)

fun reassoc( e : expr ) : expr
  match e
    Add(e1,e2) -> append-add(reassoc(e1), reassoc(e2))
    Mul(e1,e2) -> append-mul(reassoc(e1), reassoc(e2))
    _ -> e

fun show( e : expr ) : string
  match e
    Var(i)   -> "x" ++ i.show
    Val(i)   -> i.show
    Add(l,r) -> "(" ++ l.show ++ "+" ++ r.show ++ ")"
    Mul(l,r) -> "(" ++ l.show ++ "*" ++ r.show ++ ")"

fun main()
  val e = Add(Add(Val(3),Val(1)),Mul(Val(2),Mul(Val(1),Var(1))))
  println(e.reassoc.show)
