// error: array capacity K names a local variable, not a constant
// A limited array's capacity names constants as a size does.
let K = 3;

fn main() {
    let K = 5;
    var a: i64[..K] = [];
    print(a.cap, " ", K);
}
