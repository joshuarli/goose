// The same snapshot rule for operands and array elements. `shared + change()`
// reads the left operand first (1 + 2); a reference variable used as the
// left operand is read at its turn too. An element passed by value is
// copied before the callee-side write that follows in the argument list,
// while the whole array passed by reference shows the write.
fn element_pair(a: i64, b: i64) {
    print("element ", a, " ", b);
}

fn array_then_value(a: i64[3]&, b: i64) {
    print("array ", a[0], " ", b);
}

fn main() {
    var shared = 1;
    fn change() -> i64 {
        shared = 10;
        return 2;
    }
    print(shared + change());
    shared = 1;
    let alias .= shared;
    print(alias + change());
    print(alias);

    var cells: i64[3] = [5, 6, 7];
    fn poke() -> i64 {
        cells[0] = 50;
        return 9;
    }
    element_pair(cells[0], poke());
    cells[0] = 5;
    array_then_value(cells, poke());
    print(cells[0]);
}
