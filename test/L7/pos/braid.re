/*@ measure len : list('a) => int */

type list('a) [v| len(v) >= 0] =
  | Nil                      => [v| len(v) = 0] 
  | Cons (x:'a, xs:list('a)) => [v| len(v) = 1 + len(xs) ]
  ;

/*@ val braid : xs:list('a) => ys:list('a) => list('a) / len(xs) + len(ys) */
let rec braid = (xs, ys) => {
  switch (xs) {
  | Nil => ys
  | Cons (x, xs') => { 
      let tl = braid(ys, xs'); 
      Cons(x, tl)
    }
  }
};
