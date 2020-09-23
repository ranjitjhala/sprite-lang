/*@ val cmp : x:int => bool[b|b <=> (x < 0)] */
let cmp = (x) => {
    let cond = x < 10;
    if (cond) {
        true
    } else {
        false
    }
};
