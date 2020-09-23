type list('a) =
  | Nil
  | Cons('a, list('a))
  ;

type olist('a) =
  | ONil
  | OCons (x:'a, xs:olist('a[v| x <= v])) 
  ;

/*@ val insert : x:'a => ys:olist('a) => olist('a) */ 
let rec insert = (x, ys) => {
  switch (ys) {
    | ONil           => let t = ONil;
                        OCons(x, t)
    | OCons(y0, ys') => let cmp = x > y0;
                        if (cmp){
                          let tl = OCons(y0, ys');
                          OCons(x, tl)
                        } else {
                          let tl = insert(x, ys');
                          OCons(y0, tl)
                        }
  }
};

/*@ val isort : list('a) => olist('a) */ 
let rec isort = (xs) => {
  switch (xs){
    | Nil         => ONil
    | Cons (h, t) => let ot = isort(t); 
                     insert(h, ot)
  }
};
