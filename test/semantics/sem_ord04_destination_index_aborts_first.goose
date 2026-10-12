// The destination's index check happens before the right side is evaluated:
// the index 3 is out of range for the length-3 array, so the assignment
// aborts without the right side's output ever being written. An
// implementation that evaluates the right side first prints "side effect".
fn effect() -> i64 {
    print("side effect");
    return 1;
}

fn main() {
    var cells: i64[3] = [1, 2, 3];
    var i = 3;
    print("before");
    cells[i] = effect();
    print("not reached");
}
