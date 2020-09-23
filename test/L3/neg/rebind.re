/*@ val cassert : bool[b|b] => int */
let cassert = (b) => { 0 };

/*@ val check : int => int */
let check = (y) => {
  let y1  = y-1;
  let ok  = y <= y1;
  cassert(ok)
};
