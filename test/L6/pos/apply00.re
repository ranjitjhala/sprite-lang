
type list('a) =
  | Nil
  | Cons('a, list('a))
  ;

/*@ val fold_right : ('a => 'b => 'b) => 'b => list('a) => 'b */
let rec fold_right = (f, b, xs) => {
  switch (xs) {
    | Nil        => b
    | Cons(h, t) => let res = fold_right(f, b, t); 
                    f(h, res)
  }
};
