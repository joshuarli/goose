// When the left side does not decide, the right side runs, in order, once:
// `true && write()` and `false || write()` write; the nested form runs only
// the right sides it needs. The counter records how many right sides ran
// (three). An implementation that never evaluates the right side of a
// result it can compute, or evaluates it twice, prints another count.
fn main() {
    var count = 0;
    fn tick(result: bool) -> bool {
        count += 1;
        return result;
    }
    print(true && tick(true));
    print(false || tick(false));
    print(true && (false || tick(true)));
    print(false && (true || tick(true)));
    print(count);
}
