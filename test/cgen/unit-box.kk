// Constructors with unit fields have header-only blocks, while Empty is immediate.
type token
  First(value : ())
  Second(value : ())
  Empty

noinline fun flip(t : token) : token
  match t
    First(u) -> Second(u)
    Second(u) -> First(u)
    Empty -> First(())

fun label(t : token) : string
  match t
    First(_) -> "first"
    Second(_) -> "second"
    Empty -> "empty"

// A thunk with unit fields still needs enough room for an indirection.
type answer
  Done(value : ())
  lazy Delayed(value : ()) -> Done(value)

noinline fun eval-answer(a : answer) : div int
  match a
    Done(_) -> 42

fun main()
  val t = First(())
  flip(t).label.println
  t.label.println
  flip(Second(())).label.println
  flip(Empty).label.println
  val a = Delayed(())
  eval-answer(a).println
  eval-answer(a).println
