/*@ val cassert : bool[b|b] => int */
let cassert = (b) => { 
  0 
};

/*@ val abs : x:int => int[?] */
let abs = (x) => {
  let pos = 0 <= x;
  if (pos) {
     x
  } else {
     0 - x
  }
};

/*@ val incf: int => int */
let incf = (x) => {
  /*@ val wrap : (int => int[?]) => int[?] */
  let wrap = (f) => {
    let r = f(x);
    r 
  };
  let res = wrap(abs);
  let ok  = 0 < res;
  cassert (ok)
};
