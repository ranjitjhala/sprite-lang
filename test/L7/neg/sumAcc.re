/*@ val sumAcc : total:int => n:int => int / total */
let rec sumAcc = (total, n) => {
  let cond = n <= 0;
  if (cond) {
    total
  } else {
    let n1 = n - 1;
    let tot1 = total + n;
    sumAcc(tot1, n1)
  }
};