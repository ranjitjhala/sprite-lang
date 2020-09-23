/*@ reflect sum : n:int => int / n */
let rec sum = (n) => {  
  let base = n <= 0;
  if (base) {
    0
  } else {
    let n1 = n - 1;
    let t1 = sum(n1);
    n + t1
  }
};

/*@ val sum_3_eq_6 : int => int[v| sum(2) = 6] */
let sum_3_eq_6 = (x) => {
  0
};

/*@ val thm_sum : n:int[v| 0 <= v] => int[v| 2 * sum(n) = n * (n+1)] / n */
let rec thm_sum = (n) => {
  let base = n <= 0;
  if (base) {
    0
  } else {
    let n1 = n - 1;
    thm_sum(n1)
  }
};

