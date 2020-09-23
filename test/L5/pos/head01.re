
/*@ measure len : list('a) => int */

type list('a) =
  | Nil                      => [v| len v = 0] 
  | Cons (x:'a, xs:list('a)) => [v| len v = 1 + len(xs)]
  ;

/*@ val head : list('a)[v|len v > 0] => 'a */
let head = (xs) => {
  switch(xs){
    | Cons(h, t) => h
    | Nil        => impossible(0)
  }
};

/*@ val singleton : 'a => list('a)[v|len v = 1] */
let singleton = (x) => {
  let t = Nil;
  Cons(x, t)
};

/*@ val check : x:int => int */ 
let check = (z) => {
  let l = singleton(z);
  head(l)
};
