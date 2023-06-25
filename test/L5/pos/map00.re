
/*@ qualif EqLen(v:list('a), x:list('b)): (len(v) = len(x)) */

/*@ measure len : list('a) => int */

type list('a) =
  | Nil                      => [v| len v = 0]
  | Cons (x:'a, xs:list('a)) => [v| len v = 1 + len(xs)]
  ;

/*@ val length: xs:list('a) => int[v|v = len(xs)] */
let rec length = (xs) => {
  switch (xs) {
    | Nil        => 0
    | Cons(h, t) => let nt = length(t);
                    nt + 1
  }
};

/*@ val lAssert: bool[b|b] => int */
let lAssert = (x) => { 0 } ;

// SAFE with this signature
/* val map: ('a => 'b) => xs:list('a) => list('b)[v|len(v) = len(xs)]  */

// SAFE with this signature (if you use qualifier above)
/*@ val map: ('a => 'b) => xs:list('a) => list('b)[?]  */
let rec map = (f, xs) => {
  switch (xs) {
    | Nil        => Nil
    | Cons(h, t) => let y = f(h);
                    let rest = map(f, t);
                    Cons(y, rest)
  }
};

/*@ val id: (int) => int */
let id = (x) => { x };

/*@ val test_map : (list(int)) => int */
let test_map = (ys) => {
  let zs = map(id, ys);
  let nys = length(ys);
  let nzs = length(zs);
  let b = (nzs == nys);
  lAssert(b)
};