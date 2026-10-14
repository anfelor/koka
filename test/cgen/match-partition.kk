// Exhaustive dispatch across multiple partitions, including singleton sides,
// borrowed scrutinees, guard fallbacks and recursive constructor payloads.
type item
  Zero
  One
  Two
  Number(n : int)
  Text(s : string)
  Nested(x : item)
  Pair(left : item, right : item)

noinline fun score(x : item) : int
  match x
    Zero -> 0
    One -> 1
    Two -> 2
    Number(n) | n > 0 -> n
    Number(_) -> -1
    Text(s) -> s.count
    Nested(y) -> 10 + score(y)
    Pair(l,r) -> score(l) + score(r)

noinline fun copy-item(x : item) : item
  match x
    Zero -> Zero
    One -> One
    Two -> Two
    Number(n) -> Number(n + 1)
    Text(s) -> Text(s ++ "!")
    Nested(y) -> Nested(copy-item(y))
    Pair(l,r) -> Pair(copy-item(l),copy-item(r))

// Interleaved representations cannot use a single pointer partition.
type mixed
  First
  A(n : int)
  Middle
  B(n : int)
  Last
  C(n : int)

noinline fun mixed-score(x : mixed) : int
  match x
    First -> 0
    A(n) -> n
    Middle -> 2
    B(n) -> n
    Last -> 4
    C(n) -> n

fun main()
  [Zero,One,Two,Number(3),Number(-3),Text("hello"),Nested(Number(4)),Pair(One,Number(5))].foreach fn(x)
    println(score(x))
    println(score(copy-item(x)))
    println(score(x))
  [First,A(1),Middle,B(3),Last,C(5)].foreach fn(x)
    println(mixed-score(x))
