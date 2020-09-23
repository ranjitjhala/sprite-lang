
type olist('a) =
  | ONil
  | OCons (x:'a, xs:olist('a[v| x < v])) 
  ;

/*@ val foo : n:int => olist(int) */
let foo = (n) => {
  let n0 = n;
  let n1 = n0 + 1;
  let l2 = ONil;
  let l1 = OCons(n1, l2);
  let l0 = OCons(n0, l1);
  l0
};
