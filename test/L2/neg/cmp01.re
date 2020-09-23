/*@ val cmp : x:int => y:int => bool[b|b <=> (x < y)] */
let cmp = (x, y) => {
    let cond = x > y;
    if (cond) {
        true
    } else {
        false
    }
};
