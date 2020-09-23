/*@ val cassert : bool[b|b] => int */
let cassert = (b) => { 
  0 
};

/*@ val main : int => int */
let main = (x) => {
  let x1   = x - 1;
  let cond = x < x1;
  cassert(cond)
};
