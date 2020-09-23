
type list('a) =
  | Nil
  | Cons('a, list('a))
  ;

/*@ val singleton : 'a => list('a) */
let singleton = (x) => {
  let t = Nil;
  Cons(x, t)
};

/*@ val head : list('a) => 'a */
let head = (xs) => {
  switch(xs){
    | Cons(h,t) => h
    | Nil       => diverge(0)
  }
}; 

/*@ val check : x:int[v|0 <= v] => int[v|0 <= v] */ 
let check = (z) => {
  let l = singleton(z);
  head(l)
};