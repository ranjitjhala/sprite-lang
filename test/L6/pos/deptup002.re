type pair() =
  | MkPair(x:int, y:int[v|x < v])
  ;

/*@ val cassert : bool[b|b] => int */
let cassert = (b) => {
  0
};

/*@ val check1 : pair() => int */ 
let check1 = (p) => {
  switch (p){
   | MkPair(z1, z2) => let cond = z1 < z2;
                       cassert(cond) 
  }
};