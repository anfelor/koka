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
