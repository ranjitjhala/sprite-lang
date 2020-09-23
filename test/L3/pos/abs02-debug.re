/*@ val cassert : bool[b|b] => int */
let cassert = (b) => { 0 };

/*@ val abs : x:int => int[v1|v1>=0] */
let abs = (x) => { 10 };

/*@ val incf: int => int */
let incf = (z) => {
  /*@ val wrap : (y:int => int[?]) => int[v2|v2>=0]  */
  let wrap = (f) => {
    let r = f(z);
    r 
  };
  wrap(abs)
};
