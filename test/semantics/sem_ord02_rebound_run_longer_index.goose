// The same rebinding with different lengths: the original run has three
// elements and the replacement one. The index 2 is valid only for the
// original run, so reading it must succeed and give 30; a check against the
// replacement's length 1 aborts.
fn main() {
    var long: i64[>..] = [10, 20, 30];
    var short: i64[>..] = [40];
    var view: i64[:] = long[0..3];
    fn switch_view() -> i64 {
        view = short[0..1];
        return 2;
    }
    print(view[switch_view()]);
    print(view.len);
}
