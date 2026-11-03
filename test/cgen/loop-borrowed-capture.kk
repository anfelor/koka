// A self tail-recursive function becomes a loop. Its borrowed parameters that every
// iteration passes on unchanged are captured by the loop instead of being loop variables.
noinline fun count-below( ^xs : list<int>, ^limit : int, acc : int ) : int
  match xs
    Cons(x,rest) -> if x < limit then count-below(rest,limit,acc + 1) else count-below(rest,limit,acc)
    Nil -> acc

noinline fun find-key( ^kvs : list<(int,string)>, ^key : int, ^default : string ) : string
  match kvs
    Cons((k,v),rest) -> if k == key then v else find-key(rest,key,default)
    Nil -> default

// The loop does not quantify over `a`, which no call changes, so it can capture `pred`.
noinline fun count-if( ^xs : list<a>, ^pred : a -> bool, acc : int ) : int
  match xs
    Cons(x,rest) -> count-if(rest,pred,if pred(x) then acc + 1 else acc)
    Nil -> acc

fun main()
  val big = 1000000000000000000000000000000
  val xs = [1,big,3,big + 1,5]
  println(count-below(xs,10,0))
  println(count-below(xs,big + 1,0))
  val kvs = [(1,"one"),(big,"big"),(3,"three")]
  println(find-key(kvs,big,"none"))
  println(find-key(kvs,4,"none"))
  println(count-if(xs,fn(x) x > 2,0))
  println(count-if(kvs,fn(kv) kv.snd.count > 3,0))
