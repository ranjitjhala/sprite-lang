
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

/*@ val maxInt : forall (p : int => bool). x:int[v|p v] => y:int[v|p v] => int */
let maxInt = (x, y) => {
  let b = x < y;
  if (b){
    y
  } else {
    x
  }
};

/*@ val maxInts : forall (quxx: int => bool). list(int[v| quxx v]) => int[v| quxx v] */ 
let maxInts = (xs) => {
  switch (xs){
    | Cons(h, t) => let maxInt_inst = maxInt; 
                    fold_right(maxInt_inst, h, t)
    | Nil        => diverge(0)
  }
};

/*@ val maxPoss : list(int[v|0 <= v]) => int[v|0 < v] */ 
let maxPoss = (xs) => {
  maxInts(xs)
};

/*@ val maxNegs : list(int[v|v<=0]) => int[v|v<=0] */ 
let maxNegs = (xs) => {
  maxInts(xs)
};
