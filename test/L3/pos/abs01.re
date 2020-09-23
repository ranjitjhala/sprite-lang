/*@ val cassert : bool[b|b] => int */
let cassert = (b) => { 0 };

/*@ val abs : x:int => int[?] */
let abs = (x) => {
  let pos = x >= 0;
  if (pos) {
    x
  } else {
    0 - x
  }
};

/*@ val main : int => int */
let main = (y) => {
  let ya  = abs(y); 
  let ok  = 0 <= ya;
  cassert(ok)
};
