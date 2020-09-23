/*@ qualif Pos(v:int): (0 <= v) */

/*@ val foldn : ('a => int[v|0<=v] => 'a) => 'a => i:int[v|0 <= v] => n:int[v|i<=v] => 'a */
let rec foldn = (f, acc, i, n) => {
  let leq = i < n;
  if (leq) {
    let ip   = i + 1;
    let accp = f(acc, i);
    foldn(f, accp, ip, n)
  } else { 
    acc
  }
};

/*@ val add : x:int => y:int => int[v|v = x + y] */
let add = (x, y) => {
  x + y
};

/*@ val main : m:int[v|0<=v] => int[v|0<=v] */
let main = (m) => {
  foldn(add, 0, 0, m)
};
