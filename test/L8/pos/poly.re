/*@ reflect cheq : 'a => 'a => bool / 0 */
let rec cheq = (x, y) => { 
  x == y 
};

/*@ val test_int : int => int[v| cheq(2, 2) ] */
let test_int = (x) => {
  0
};

/*@ val test_bool : int => int[v| cheq(true, true) ] */
let test_bool = (x) => {
  0
};



