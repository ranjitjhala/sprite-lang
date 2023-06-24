

/*@ val inc: x:int => int[v|v=x+1] */
let inc = (x) => {
    x + 1
};

/*@ val incf: x:int[v|0<=v] => int[v|0<=v] */
let incf = (x) => {
    /*@ val tmp : f:(z:int[v|0<=v] => int[v|0<=v]) => int[v|0<=v] */
    let tmp = (f) => {
        f(x)
    };
    tmp(inc)
};
