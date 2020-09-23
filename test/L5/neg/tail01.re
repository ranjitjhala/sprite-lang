/*@ measure len : list('a) => int */

type list('a) =
  | Nil                      => [v| len v = 0] 
  | Cons (x:'a, xs:list('a)) => [v| len v = 1 + len(xs)]
  ;

/*@ val tail: zs:list('a)[v|len v > 0] => list('a)[v|len v = len(zs) - 2] */
let tail = (zs) => {
  switch(zs){
    | Cons(h, t) => t
    | Nil        => impossible(0)
  }
};
