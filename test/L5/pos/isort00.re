
/*@ measure len : list('a) => int */

type list('a) =
  | Nil                      => [v| len v = 0] 
  | Cons (x:'a, xs:list('a)) => [v| len v = 1 + len(xs)]
  ;


/*@ val insert : x:'a => ys:list('a) => list('a)[v|len v = 1 + len(ys)] */ 
let rec insert = (x, ys) => {
  switch (ys) {
    | Nil           => let t = Nil;
                       Cons(x, t)
    | Cons(y0, ys') => let cmp = x <= y0;
                       if (cmp){
                          let tl = Cons(y0, ys');
                          Cons(x, tl)
                        } else {
                          let tl = insert(x, ys');
                          Cons(y0, tl)
                        }
  }
};

/*@ val isort : xs:list('a) => list('a)[v|len(v) = len(xs)] */ 
let rec isort = (xs) => {
  switch (xs){
    | Nil         => Nil
    | Cons (h, t) => let ot = isort(t); 
                     insert(h, ot)
  }
};