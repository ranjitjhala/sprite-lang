/*@ val inc: x:int[v|0<=v] => int[v|0<=v] */
let inc = (x) => {
    x + 1
};

/*@ val dec : x:int => int[v | v == x - 1] */
let dec = (x) => {
    x - 1
};

/*@ val inc2: x:int[v|0<=v] => int[v|0<=v] */
let inc2 = (x) => {
    let tmp = inc(x);
    dec(tmp)
};

