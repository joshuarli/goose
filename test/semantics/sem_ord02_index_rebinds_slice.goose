// The index expression rebinds the slice variable being indexed. The access
// uses the run (and length) sampled before the index ran, so it reads the
// original array; afterwards the variable designates the other array. An
// implementation that reloads the variable after the index reads 40.
fn main() {
    var first: i64[>..] = [10, 20, 30];
    var second: i64[>..] = [40];
    var view: i64[:] = first[0..3];
    fn switch_view() -> i64 {
        view = second[0..1];
        return 0;
    }
    print(view[switch_view()]);
    print(view[0], " ", view.len);
}
