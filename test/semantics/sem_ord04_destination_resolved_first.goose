// The destination of an assignment is resolved, index check included, before
// the right side runs. `next` moves the index to 1 and returns 9; the plain
// and the compound assignment both still write element 0. The compound form
// also reads the old element 0 (5) before the right side. A destination
// resolved late writes element 1 instead.
fn main() {
    var cells: i64[3] = [5, 6, 7];
    var i = 0;
    fn next() -> i64 {
        i = 1;
        cells[0] = 100;
        return 9;
    }
    cells[i] = next();
    print(cells[0], " ", cells[1], " ", cells[2]);
    i = 0;
    cells[0] = 5;
    cells[i] += next();
    print(cells[0], " ", cells[1], " ", cells[2]);
}
