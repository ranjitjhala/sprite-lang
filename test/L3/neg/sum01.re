/*@ val cassert : bool[b|b] => int */
let cassert = (b) => { 0 };

/*@ val sum : n:int => int[?] */
let rec sum = (n) => {
    let cond = n <= 0;
    if (cond) {
        0
    } else {
        let n1 = n-1;
        let t1 = sum(n1);
        n + t1
    }
};

/*@ val check2 : int => int */
let check2 = (y) => {
  let y1  = y-1;
  let res = sum(y1); 
  let ok  = y <= res;
  cassert(ok)
};
