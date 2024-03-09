/*@ measure len : list('a) => int */

type list('a) [v|len(v) >= 0] =
  | Nil                      => [v| v = Nil && len v = 0]
  | Cons (x:'a, xs:list('a)) => [v| v = Cons(x, xs) && len v = 1 + len(xs)]
  ;

/*@ reflect append : xs:list('a) => list('a) => list('a) / len(xs) */
let rec append = (xs, ys) => {
  switch (xs) {
  | Nil        => ys
  | Cons(h, t) => let rest = append(t, ys);
                  Cons(h, rest)
  }
};

/*@ val append_12_34 : int => int[v|append(Cons(1, Cons(2, Nil)), Cons(3, Cons(4, Nil))) = Cons(1, Cons(2, Cons(3, Cons(4, Nil))))] */
let append_12_34 = (x) => {
  0
};

/*@ val append_assoc : xs:list('a) => ys:list('a) => zs:list('a) =>
                     int[v|append(append(xs, ys), zs) = append(xs, append(ys, zs))] / len(xs)
 */
let rec append_assoc = (xs, ys, zs) => {
  switch (xs) {
  | Nil          => 0
  | Cons(x, xs') => append_assoc(xs', ys, zs)
  }
};
