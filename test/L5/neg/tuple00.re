
type coord = 
  | C (x:int, y:int[v|x < v])
  ;

/*@ val cassert : bool[b|b] => int */
let cassert = (b) => { 
  0 
};

/*@ val mk : n:int => coord */
let mk = (n) => { 
  let n1 = n + 1;
  C(n1, n1) 
};

/*@ val check : m:int => int */
let check = (m) => {
    let p = mk(m);
    switch (p){
      | C(px, py) => let ok = px < py;
                     cassert(ok)
    }
};
