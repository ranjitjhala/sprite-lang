
type list('a) =
  | Nil
  | Cons('a, list('a))
  ;

/*@ val maxInt : forall (p : int => bool). x:int[v|p v] => y:int[v|p v] => int[v|p v] */
let maxInt = (x, y) => {
  let b = x < y;
  if (b){
    y
  } else {
    x
  }
};

/* val maxInts : forall (p : int => bool). int[v| p v] => list(int[v| p v]) => int[v| p v] */ 
/*@ val maxInts : int => list(int) => int */ 
let rec maxInts = (cur, xs) => {
  switch (xs) {
    | Cons(h, t) => let newCur = maxInt(cur, h); 
                    maxInts(newCur, t)
    | Nil        => (cur)
  }
};

/*@ val maxPoss : list(int[v|0 <= v]) => int[v|0<=v] */ 
let maxPoss = (xs) => {
  maxInts(0, xs)
};
