// Borrowed guard operands stay borrowed after being loaded. Exercise both
// taking a unique payload and copying a shared one, including heap integers.
type entry
  Empty
  Entry(rank : int, key : int, rest : list<int>)

noinline fun above( ^x : int, ^y : int ) : bool
  x > y

noinline fun update( e : entry, limit : int ) : entry
  match e
    Entry(r,k,xs) | above(r,limit) && above(k,limit)
      -> Entry(r + 1,k + 1,xs)
    _ -> e

// The key is conditional in the guard and reused after it, including when the
// first comparison succeeds and the key comparison is skipped.
noinline fun update-either( e : entry, limit : int ) : entry
  match e
    Entry(r,k,xs) | above(r,limit) || above(k,limit)
      -> Entry(r + 1,k + 1,xs)
    _ -> e

// With no later key use, its read should stay in the short-circuit branch.
noinline fun qualifies( ^e : entry, limit : int ) : bool
  match e
    Entry(r,k,_) -> above(r,limit) || above(k,limit)
    _ -> False

noinline fun show-entry( ^e : entry ) : string
  match e
    Empty -> "empty"
    Entry(r,k,xs) -> r.show ++ ":" ++ k.show ++ ":" ++ xs.show

noinline fun shared( e : entry )
  val next = update(e,0)
  println(show-entry(e))
  println(show-entry(next))
  println(show-entry(update-either(e,0)))

fun main()
  val big = 1000000000000000000000000000000
  println(show-entry(update(Entry(big,big + 2,[1,2]),0)))
  shared(Entry(big,big + 2,[3,4]))
  println(show-entry(update(Entry(1,2,[]),3)))
  println(show-entry(update(Entry(3,1,[]),2)))
  println(show-entry(update(Empty,0)))
  println(show-entry(update-either(Entry(big,1,[]),2)))
  println(show-entry(update-either(Entry(1,big,[]),2)))
  println(show-entry(update-either(Entry(1,1,[]),2)))
  println(qualifies(Entry(big,1,[]),2))
