
type olist('a) =
  | ONil
  | OCons (x:'a, xs:olist('a[v| x < v])) 
  ;

/*@ val bar : apple:int => horse: olist(int) => olist(int) */
let bar = (apple, horse) => {
  OCons (apple, horse)
};
