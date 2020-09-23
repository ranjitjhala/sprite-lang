
/*@ val choose : 'a => 'b => 'b */
let choose = (x, y) => { y };

/*@ val check : int[v|0<=v] => int[v|0<=v] => int[v|0<=v] */
let check = (a, b) => {
  let aM  = a - 1;
  let res = choose(aM, a); 
  res
};
