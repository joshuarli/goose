// A fixed array passed by value is a copy: the callee's write is not seen by
// the caller. The same array passed by reference is the caller's array, and
// the write is seen, also through the reference the caller held before the
// call. A slice parameter writes through to the elements it views.
fn write_copy(cells: i64[3]) -> i64 {
    var mine = cells;
    mine[0] = 99;
    return mine[0];
}

fn write_reference(cells: i64[3]&) {
    cells[0] = 99;
}

fn write_slice(cells: i64[:]) {
    cells[2] = 77;
}

fn main() {
    var cells: i64[3] = [1, 2, 3];
    let held .= cells[0];
    print(write_copy(cells), " ", cells[0], " ", held);
    write_reference(cells);
    print(cells[0], " ", held);
    write_slice(cells[0..3]);
    print(cells[2]);
}
