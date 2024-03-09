/*@ measure len : list('a) => int */

type list('a) [v|len(v) >= 0] =
  | Nil                      => [v| len(v) = 0]
  | Cons (x:'a, xs:list('a)) => [v| len(v) = 1 + len(xs)]
  ;

/*@ val append : xs:list('a) => list('a) => list('a) / len(xs) */
let rec append = (xs, ys) => {
  switch (xs) {
  | Nil        => ys
  | Cons(h, t) => let rest = append(t, ys);
                  Cons(h, rest)
  }
};
