type pair()(zog : int => int => bool) =
  | MkPair(x:int, y:int[v|zog x v])
  ;

/*@ val cassert : bool[b|b] => int */
let cassert = (b) => {
  0
};

/*@ val check1 : pair()((x1:int, x2:int) => x1 < x2) => int */ 
let check1 = (p) => {
  switch (p){
   | MkPair(z1, z2) => let cond = z1 < z2;
                       cassert(cond) 
  }
};