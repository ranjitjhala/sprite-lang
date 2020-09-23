/*@ measure len : list('a) => int */

type list('a) =
  | Nil                      => [v| len v = 0] 
  | Cons (x:'a, xs:list('a)) => [v| len v = 1 + len(xs)]
  ;

/*@ val append : xs:list('a) => ys:list('a) => list('a)[v|len v = len(xs) + len(ys)] */
let rec append = (xs, ys) => {
  switch (xs) {
    | Nil        => ys 
    | Cons(h, t) => append(t, ys)
  }
}; 
