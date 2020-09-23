
/*@ val choose : 'a => 'b => 'a */
let choose = (x, y) => { x };

/*@ val check : int[v|0<=v] => int[v|0<=v] => int[v|0<=v] */
let check = (a, b) => {
  let aM  = a - 1;
  let res = choose(aM, a); 
  res
};
