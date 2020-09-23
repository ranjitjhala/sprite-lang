/*@ measure len : list('a) => int */
/*@ measure elts : list('a) => Set_Set('a) */

type list('a) [v|len(v) >= 0] =
  | Nil                      => [v| v = Nil && len(v) = 0 && elts(v) = Set_empty(0)]  
  | Cons (x:'a, xs:list('a)) => [v| v = Cons(x, xs) && len (v) = 1 + len(xs) && elts(v) = Set_add(elts(xs), x)]
  ;

/*@ val app : xs:list('a) => ys:list('a) => list('a)[v|elts(v) = Set_cup(elts(xs), elts(ys))] / len(xs) */
let rec app = (xs, ys) => {
  switch (xs) {
  | Nil        => ys 
  | Cons(h, t) => let rest = app(t, ys);
                  Cons(h, rest) 
  }
};