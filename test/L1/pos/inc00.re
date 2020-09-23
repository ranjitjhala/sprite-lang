

/*@ val inc: x:int => int[v|v = x + 1] */
let inc = (x) => {
    x + 1
};

let bar = inc(10);
