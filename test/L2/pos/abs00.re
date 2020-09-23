/*@ val abs : x:int => int[v|0<=v] */
let abs = (x) => { 
    let pos = x >= 0; 
    if (pos) {
        x
    } else {
        0 - x
    }
};
