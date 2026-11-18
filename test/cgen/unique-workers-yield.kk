// Unique workers (`UniqueWorkers`) of functions that may yield: a helper that extends a
// context and calls an operation gets a worker with a unique context and a result that is
// unique unless it is the dummy of a yield. Resuming more than once must not share an
// accumulator that is appended in place.

effect choose
  ctl flip() : bool

type deriv
  Left(x : int)
  Right(x : int)
  Keep

// extends a context by a derivative, or keeps it, after asking which sign to use
noinline fun extend(acc : ctx<list<int>>, d : deriv) : choose ctx<list<int>>
  match d
    Left(x) -> if flip() then acc ++ ctx Cons(x, hole) else acc ++ ctx Cons(0 - x, hole)
    Right(x) -> acc ++ ctx Cons(x * 10, hole)
    Keep -> acc

// the loop calls the worker
fun walk(xs : list<int>, acc : ctx<list<int>>) : <choose,div> list<int>
  match xs
    Cons(x, xx) -> walk(xx, extend(acc, if x % 3 == 0 then Keep elif x % 2 == 0 then Left(x) else Right(x)))
    Nil -> acc ++. Nil

// every choice
fun all(action : () -> <choose|e> a) : e list<a>
  with ctl flip() append(resume(True), resume(False))
  [action()]

// only the first choice
fun first(action : () -> <choose|e> a) : e a
  with fun flip() True
  action()

fun main()
  val shared = ctx Cons(0, hole)
  all{ walk([1, 2, 3, 4], shared) }.show.println
  all{ walk([2, 4, 6, 8], shared) }.show.println
  first{ walk([2, 4, 5], shared) }.show.println
  val c1 = first{ extend(shared, Left(7)) }
  (c1 ++. Nil).show.println
  (shared ++. Nil).show.println
