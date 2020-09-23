
type olist('a) =
  | ONil
  | OCons (x:'a, xs:olist('a[v| x < v])) 
  ;

/*@ val foo : n:int => olist(int) */
let foo = (n) => {
  let n0 = n + 1;
  let n1 = n;
  let l2 = ONil;
  let l1 = OCons(n1, l2);
  let l0 = OCons(n0, l1);
  l0
};
