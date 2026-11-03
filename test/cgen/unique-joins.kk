// Contexts in loops (`UniqueJoins`): a loop parameter that only receives unique
// contexts is unique, copied once at the entry instead of at every append.

// appends to the accumulator directly: the only copy is at the entry
fun build(n : int, acc : ctx<list<int>>) : div list<int>
  if n <= 0 then acc ++. Nil
  else build(n - 1, acc ++ ctx Cons(n, hole))

// the accumulator is used twice in the loop (`dup`): the copies stay
fun prefixes(n : int, acc : ctx<list<int>>, keep : list<list<int>>) : div list<list<int>>
  if n <= 0 then keep
  else prefixes(n - 1, acc ++ ctx Cons(n, hole), Cons(acc ++. Nil, keep))

// a closure inside the loop captures the accumulator
fun thunks(n : int, acc : ctx<list<int>>, fs : list<() -> list<int>>) : div list<() -> list<int>>
  if n <= 0 then fs
  else thunks(n - 1, acc ++ ctx Cons(n, hole), Cons(fn() acc ++. Nil, fs))

// a non-recursive join point (the shared last alternative) carries the accumulator into the jump
fun pairs(xs : list<int>, acc : ctx<list<int>>) : list<int>
  match xs
    Cons(x, Cons(y, yy)) | x == y -> pairs(yy, acc ++ ctx Cons(x, hole))
    Cons(x, xx) -> pairs(xx, acc ++ ctx Cons(x * 10, hole))
    Nil -> acc ++. Nil

// a multi-shot handler resumes inside the loop with a captured accumulator
effect choose
  ctl flip() : bool

fun pick(n : int, acc : ctx<list<int>>) : <choose,div> list<int>
  if n <= 0 then acc ++. Nil
  elif flip() then pick(n - 1, acc ++ ctx Cons(n, hole))
  else pick(n - 1, acc ++ ctx Cons(0 - n, hole))

fun choices(action : () -> <choose,div> list<int>) : div list<list<int>>
  with ctl flip() list/(++)(resume(True), resume(False))
  [action()]

fun main()
  // a shared accumulator: every use must see its own copy
  val shared = ctx Cons(0, hole)
  build(3, shared).show.println
  build(2, shared).show.println
  prefixes(3, ctx hole, []).show.println
  thunks(3, shared, []).map(fn(f) f()).show.println
  pairs([1, 1, 2, 3, 3, 4], shared).show.println
  choices(fn() pick(2, shared)).show.println
