// The bounds of a range loop are evaluated once, before the first iteration.
// The loop pushes while it runs, and its end `items.len` is read at the
// start (3): exactly three iterations run, though the array ends with six
// elements. An implementation that rereads the bound never terminates the
// way this program does. An empty or reversed range runs no iteration.
fn main() {
    var items: i64[>..] = [10, 20, 30];
    var iterations = 0;
    for i in 0..items.len {
        items.push(items[i] + 1);
        iterations += 1;
    }
    print(iterations, " ", items.len, " ", items[5]);

    var empty = 0;
    for i in 5..2 {
        empty += 1;
    }
    for i in 3..3 {
        empty += 1;
    }
    print(empty);
}
