
type list('a) =
  | Nil
  | Cons('a, list('a))
  ;

/*@ val singleton : int[v|0 <= v]  => list(int[v|0 <= v]) */
let singleton = (x) => {
  let t = Nil;
  Cons(x, t)
};
