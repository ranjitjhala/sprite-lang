/*@ val ack : m:int[v|0 <= v] => n:int[v|0 <= v] => int / m, n */
let rec ack = (m, n) => {
  let condm = m == 0;
  let condn = n == 0;
  if (condm) { 
    n + 1 
  } else {
    let m1 = m - 1;
    if (condn) { 
      ack (m1, 1) 
    } else {
      let n1 = n - 1;
      let r  = ack(m, n1);
      ack (m1, r)
    }
  }
};
