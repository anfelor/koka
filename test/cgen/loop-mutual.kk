// Functions that call each other in tail position share a loop: a worker takes the
// arguments of one of them, and each function wraps it.
noinline fun is-even-nat( n : int ) : div bool
  if n == 0 then True else is-odd-nat(n - 1)

noinline fun is-odd-nat( n : int ) : div bool
  if n == 0 then False else is-even-nat(n - 1)

// a state machine whose states take different parameters
noinline fun words( cs : list<char>, count : int ) : div int
  match cs
    Cons(' ',rest) -> words(rest,count)
    Cons(_,rest)   -> in-word(rest,count + 1,1)
    Nil            -> count

noinline fun in-word( cs : list<char>, count : int, len : int ) : div int
  match cs
    Cons(' ',rest) -> words(rest,count)
    Cons(_,rest)   -> in-word(rest,count,len + 1)
    Nil            -> count

// parameters of different modes: the worker's sum has one mode, so each stays a loop of its own
noinline fun count-up( ^xs : list<int>, ^limit : int, acc : int ) : div int
  match xs
    Cons(x,rest) -> if x < limit then count-up(rest,limit,acc + 1) else count-down(rest,limit,acc)
    Nil -> acc

noinline fun count-down( ^xs : list<int>, ^limit : int, acc : int ) : div int
  match xs
    Cons(x,rest) -> if x < limit then count-up(rest,limit,acc) else count-down(rest,limit,acc - 1)
    Nil -> acc

// borrowed parameters: the worker borrows the sum
noinline fun find-up( ^xs : list<int>, ^limit : int ) : div int
  match xs
    Cons(x,rest) -> if x < limit then find-up(rest,limit) else find-down(rest,limit)
    Nil -> limit

noinline fun find-down( ^xs : list<int>, ^limit : int ) : div int
  match xs
    Cons(x,rest) -> if x < limit then find-up(rest,x) else find-down(rest,limit)
    Nil -> 0 - limit

// type parameters that are not in the result, which the calls change
noinline fun alternate( xs : list<a>, ys : list<b>, n : int ) : div int
  match xs
    Cons(_,rest) -> alternate2(ys,rest,n + 1)
    Nil -> n

noinline fun alternate2( ys : list<b>, xs : list<a>, n : int ) : div int
  match ys
    Cons(_,rest) -> alternate(xs,rest,n + 10)
    Nil -> n

// the results agree up to a renaming of their type parameters
noinline fun take-even( xs : list<a>, acc : list<a> ) : div list<a>
  match xs
    Cons(x,rest) -> take-odd(rest,Cons(x,acc))
    Nil -> acc.reverse

noinline fun take-odd( ys : list<b>, acc : list<b> ) : div list<b>
  match ys
    Cons(_,rest) -> take-even(rest,acc)
    Nil -> acc.reverse

fun main()
  println(is-even-nat(100001))
  println(is-odd-nat(100001))
  println(words("  the quick  brown fox ".list,0))
  println(count-up([1,5,2,7,8,3],4,0))
  println(find-up([1,5,2,7,8,3],4))
  println(alternate([1,2,3],["a","b"],0))
  println(take-even(list(1,10),[]).show)
  println(take-odd(["a","b","c","d"],[]).show)
