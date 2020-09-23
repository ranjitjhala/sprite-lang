/*@ val dec : x:int => int[v|v==x-1] */
let dec = (x) => {
    x - 1
};

/*@ val incf: x:int[v|0<=v] => int[v|0<=v] */
let incf = (x) => {
    /*@ val tmp : f:(int[v|0<=v] => int[v|0<=v]) => int[v|0<=v] */
    let tmp = (f) => {
        f(x)
    };
    tmp(dec)
};
