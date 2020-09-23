/*@ measure elts : list('a) => Set_Set('a) */

type list('a) =
  | Nil                      => [v| elts(v) = Set_empty(0)]  
  | Cons (x:'a, xs:list('a)) => [v| elts(v) = Set_add(elts(xs), x)]
  ;

/*@ val app : xs:list('a) => ys:list('a) => list('a)[v|elts(v) = Set_cup(elts(xs), elts(ys))] */
let rec app = (xs, ys) => {
  switch (xs) {
  | Nil        => ys 
  | Cons(h, t) => let rest = app(t, ys);
                  Cons(h, rest) 
  }
};
