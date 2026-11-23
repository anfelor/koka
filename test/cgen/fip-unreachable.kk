// A `fip` function may complete a match with `unreachable()`: FIP checking ignores the paths
// that end in it. An incomplete match is checked as if it fails with a FIP violation.

// completed by `unreachable()`: no warnings
fip fun swap-head( xs : list<int> ) : list<int>
  match xs
    Cons(x, Cons(y, ys)) -> Cons(y, Cons(x, ys))
    _ -> unreachable()

// incomplete: warns
fip fun swap-head-partial( xs : list<int> ) : exn list<int>
  match xs
    Cons(x, Cons(y, ys)) -> Cons(y, Cons(x, ys))

pub fun main()
  println(swap-head([1,2,3]).show)
  println(swap-head-partial([4,5]).show)
  println(nested([7], BCons(BNil, Pad, Pad)).show)
  println(first-or-empty([Node(8, [])]).default([]).length)

// a nested match completed by `unreachable()` in a branch that becomes a join point: the typed
// backend once passed `unreachable` to the join as an argument (and so evaluated it)
type buffer
  BNil
  BCons(next : buffer, b : pad, c : pad)

fun nested( xs : list<int>, b : buffer ) : int
  match xs
    Nil -> 0
    Cons(x, _) ->
      match b
        BCons(_, _, _) -> x + 100
        _ -> unreachable()

// a trivial alternative (`Nil`) whose only other alternative is `unreachable()`, after a
// borrowed use: the typed backend once found that it consumes `ts` differently than `Just`
type tree
  Node( r : int, c : list<tree> )

fun last-rank( ^r : maybe<int>, ^ts : list<tree> ) : maybe<int>
  match ts
    Nil -> r
    Cons(Node(r', _), ts') -> last-rank(Just(r'), ts')

fun first-or-empty( ts : list<tree> ) : maybe<list<tree>>
  match last-rank(Nothing, ts)
    Just(_) -> Just(ts)
    Nothing -> match ts
      Nil -> Nothing
      _ -> unreachable()
