/*@ val silly : forall (p : 'a => bool). x:'a[v|p v] => 'a[v|p v] */
let silly = (x) => {
  x
};

/*@ val test1 : a:int[v|0 < v] => int[v|0 < v] */
let test1 = (apple) => {
  silly(apple)
};

