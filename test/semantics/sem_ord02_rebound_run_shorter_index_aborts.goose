// The original run has one element and the replacement three. Index 2 is
// valid in the replacement only, and the access still aborts with length 1:
// the run sampled before the index expression decides. The abort comes after
// the rebinding has happened, which the output before it shows.
fn main() {
    var short: i64[>..] = [40];
    var long: i64[>..] = [10, 20, 30];
    var view: i64[:] = short[0..1];
    fn switch_view() -> i64 {
        view = long[0..3];
        print("rebound to length ", view.len);
        return 2;
    }
    print(view[switch_view()]);
    print("not reached");
}
