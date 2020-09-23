type pair('a, 'b)(p : 'a => 'b => bool) =
  | MkPair(x:'a, y:'b[v|p x v])
  ;

/*@ val check2 : x:int => pair(int, int)((x1:int, x2:int) => x1 > x2) */ 
let check2 = (x) => {
  let y = x + 1;
  MkPair(x, y)
};
