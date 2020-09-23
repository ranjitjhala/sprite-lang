/*@ val abs : x:int => int[v|0<=v] */
let abs = (x) => { 
    let pos = x >= 0; 
    if (pos) {
        0 - x
    } else {
        x
    }
};
