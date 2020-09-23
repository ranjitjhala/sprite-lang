/*@ measure len : list('a) => int */
type list('a) [v|len(v) >= 0] =
  | Nil                      => [v| v = Nil && len(v) = 0]  
  | Cons (x:'a, xs:list('a)) => [v| v = Cons(x, xs) && len (v) = 1 + len(xs)]
  ;

/*@ reflect app : xs:list('a) => list('a) => list('a) / len(xs) */
let rec app = (xs, ys) => {
  switch (xs) {
  | Nil        => ys 
  | Cons(h, t) => let rest = app(t, ys);
                  Cons(h, rest) 
  }
};

/*@ reflect rev : xs:list('a) => list('a) / len(xs) */
let rec rev = (xs) => {
  switch (xs) {
  | Nil        => Nil
  | Cons(h, t) => let rest = rev(t);
                  let n0   = Nil;
                  let hl   = Cons(h, n0);
                  app(rest, hl) 
  }
};

/*@ reflect elts : l:list('a) => Set_Set('a) / len(l) */
let rec elts = (l) => {
  switch (l) {
  | Nil        => Set_empty(0)
  | Cons(h, t) => let rest = elts(t); 
                  Set_add(rest, h)
  }
};

/*@ val app_elts : xs:list('a) => ys:list('a) => 
                     int[v|elts(app(xs, ys)) = Set_cup(elts(xs), elts(ys))] / len(xs) 
 */
let rec app_elts = (xs, ys) => {
  switch (xs) {
  | Nil          => 0
  | Cons(x, xs') => app_elts(xs', ys)
  }
};

/*@ val rev_elts : xs:list('a) => int[v|elts(rev(xs)) = elts(xs)] / len(xs) 
 */
let rec rev_elts = (xs) => {
  switch (xs) {
  | Nil        => 0
  | Cons(h, t) => let rest = rev(t);
                  let n0   = Nil;
                  let hl   = Cons(h, n0);
                  let pf1  = rev_elts(t); 
                  let pf2  = app_elts(rest, hl);
                  0
  }
};
