type pair()(pp : int => int => bool) =
  | MkPair(x:int, y:int[v|pp x v])
  ;

/*@ val check1 : x:int => pair()((el1:int, el2:int) => el1 < el2) */ 
let check1 = (x) => {
  let y = x + 1;
  MkPair(x, y)
};
