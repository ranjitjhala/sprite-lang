/*@ val id : 'a => 'a */
let id = (x) => { x };

/*@ val check1 : x:int[v|0<=v] => int[v|0<=v] */
let check1 = (y) => {
  let y1   = y - 1;
  let res  = id(y1); 
  res
};
