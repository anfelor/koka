// A shared context can be extended in a loop or passed to a helper on its own.

type deriv
  Left(x : int)
  Right(x : int)
  Keep

// extends a context by a derivative, or keeps it
noinline fun extend(acc : ctx<list<int>>, d : deriv) : ctx<list<int>>
  match d
    Left(x) -> acc ++ ctx Cons(x, hole)
    Right(x) -> acc ++ ctx Cons(0 - x, hole)
    Keep -> acc

// this loop extends its accumulator through the helper
fun walk(xs : list<int>, acc : ctx<list<int>>) : div list<int>
  match xs
    Cons(x, xx) -> walk(xx, extend(acc, if x % 3 == 0 then Keep elif x % 2 == 0 then Left(x) else Right(x)))
    Nil -> acc ++. Nil

// an append in both branches, bound by `val`
fun split(xs : list<int>, acc : ctx<list<int>>) : div list<int>
  match xs
    Cons(x, xx) ->
      val acc' = if x % 2 == 0 then acc ++ ctx Cons(x, hole) else acc ++ ctx Cons(x * 10, hole)
      split(xx, acc')
    Nil -> acc ++. Nil

fun main()
  // a shared accumulator: every use must see its own copy
  val shared = ctx Cons(0, hole)
  walk([1, 2, 3, 4], shared).show.println
  walk([5, 6], shared).show.println
  // the helper can also extend a shared context outside the loop
  val c1 = extend(shared, Left(7))
  val c2 = extend(shared, Right(8))
  (c1 ++. Nil).show.println
  (c2 ++. Nil).show.println
  split([1, 2, 3], shared).show.println
  split([4], shared).show.println
