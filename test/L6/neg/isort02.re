type list('a)(p : 'a => 'a => bool) =
  | Nil
  | Cons(x:'a, list('a[v|p x v])((x1:'a, x2:'a) => p x1 x2))
  ;

/*@ val insert : x:'a => ys:list('a)((u1:'a, u2:'a) => u1 <= u2) => list('a)((u1:'a, u2:'a) => u1 <= u2) */ 
let rec insert = (x, ys) => {
  switch (ys) {
    | Nil           => let t = Nil;
                       Cons(x, t)
    | Cons(y0, ys') => let cmp = y0 <= x;
                        if (cmp){
                          let tl = Cons(y0, ys');
                          Cons(x, tl)
                        } else {
                          let tl = insert(x, ys');
                          Cons(y0, tl)
                        }
  }
};

/*@ val isort : list('a)((u1:'a, u2:'a) => true) => list('a)((u1:'a, u2:'a) => u1 <= u2) */ 
let rec isort = (xs) => {
  switch (xs){
    | Nil         => Nil
    | Cons (h, t) => let ot = isort(t); 
                     insert(h, ot)
  }
};
