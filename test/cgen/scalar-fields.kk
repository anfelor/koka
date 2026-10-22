import std/num/int32
import std/num/int64

// A product whose only field is a raw value or an enumeration is boxed like that field: the
// raw value as a scalar (heap-backed for a large `int64`), the enumeration by its tag.
type color
  Red
  Green
  Blue

value struct small( u : (), x : int32 )
value struct big( x : int64, u : () )
value struct tint( c : color, u : () )

value type packed
  Packed<a>( x : int32, u : () )

fun color/show( c : color ) : string
  match c
    Red -> "red"
    Green -> "green"
    Blue -> "blue"

noinline fun twice( x : a ) : list<a>
  [x,x]

fun main()
  println(twice(Small((), 41.int32)).map(fn(s) (s.x + 1.int32).show))
  println(twice(Big(0x7FFF_FFFF_FFFF_FFFE.int64, ())).map(fn(b) (b.x + 1.int64).show))
  println([Red,Green,Blue].map(fn(c) Tint(c, ())).flatmap(twice).map(fn(t) t.c.show))
  println(twice(Packed(7.int32, ())).map(fn(p) match p { Packed(x) -> x.show }))
