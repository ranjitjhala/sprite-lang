
type list('a) =
  | Nil
  | Cons('a, list('a))
  ;

/*@ val fold_right : ('alice => 'bob => 'bob) => 'bob => list('alice) => 'bob */
let rec fold_right = (f, b, xs) => {
  switch (xs) {
    | Nil        => b
    | Cons(h, t) => let res = fold_right(f, b, t); 
                    f(h, res)
  }
};
