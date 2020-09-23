/*@ measure len : list('a) => int */

type list('a) =
  | Nil                      => [v| len v = 0] 
  | Cons (x:'a, xs:list('a)) => [v| len v = 1 + len(xs)]
  ;

/*@ val range : i:int => j:int => list(int) / (j - i) */
let rec range = (i, j) => {
  let cond = (i == j);
  if (cond) {
    let i1 = i + 1;
    let tl = range(i1, j);
    Cons(i, tl)
  } else {
    Nil
  }
};
