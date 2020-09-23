/*@ val sum : n:int[v|0 <= v] => int[v|0 <= v] / n */
let rec sum = (n) => {
    let cond = n == 0;
    if (cond) {
        0
    } else {
        let n1 = n-1;
        let t1 = sum(n1);
        n + t1
    }
};