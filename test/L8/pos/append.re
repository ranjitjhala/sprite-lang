/*@ measure len : list('a) => int */

type list('a) [v|len(v) >= 0] =
  | Nil                      => [v| v = Nil && len v = 0] 
  | Cons (x:'a, xs:list('a)) => [v| v = Cons(x, xs) && len v = 1 + len(xs)]
  ;

/*@ reflect app : xs:list('a) => list('a) => list('a) / len(xs) */
let rec app = (xs, ys) => {
  switch (xs) {
  | Nil        => ys 
  | Cons(h, t) => let rest = app(t, ys);
                  Cons(h, rest) 
  }
};

/*@ val app_12_34 : int => int[v|app(Cons(1, Cons(2, Nil)), Cons(3, Cons(4, Nil))) = Cons(1, Cons(2, Cons(3, Cons(4, Nil))))] */
let app_12_34 = (x) => {
  0
};

/*@ val app_assoc : xs:list('a) => ys:list('a) => zs:list('a) => 
                     int[v|app(app(xs, ys), zs) = app(xs, app(ys, zs))] / len(xs) 
 */
let rec app_assoc = (xs, ys, zs) => {
  switch (xs) {
  | Nil          => 0
  | Cons(x, xs') => app_assoc(xs', ys, zs)
  }
};
