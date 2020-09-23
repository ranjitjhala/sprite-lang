/*@ val id : 'a => 'a */
let id = (x) => { x };

/*@ val check1 : x:int[v|0<=v] => int[v|0<=v] */
let check1 = (y) => {
  let res  = id(y); 
  res
};
