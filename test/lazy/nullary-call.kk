// A lazy constructor body whose branch ends in a call without arguments of a
// function (not a constructor): the call is kept, not replaced by the function itself.

type stream
  SNil
  SCons( i : int, rest : stream )

  lazy Copy( xs : list<int> ) ->
    match xs
      Cons(x,xx) -> SCons(x, Copy(xx))
      Nil        -> stuck()

fun stuck() : div a
  stuck()

fun head( s : stream ) : div int
  match s
    SCons(x,_) -> x
    SNil       -> 0

pub fun main()
  Copy([1,2,3]).head
