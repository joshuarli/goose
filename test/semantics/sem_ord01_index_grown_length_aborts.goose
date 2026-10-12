// The index expression pushes onto the indexed array and returns the index
// of the element it just added. That index is valid in the grown array but
// the check uses the length sampled before the index expression ran (2), so
// the access aborts with index 2 and length 2, after the callee has printed.
// An implementation that samples the length after the index prints 30.
fn grow_and_pick(items: i64[>..]&) -> i64 {
    items.push(30);
    print("pushed, length ", items.len);
    return 2;
}

fn main() {
    var items: i64[>..] = [10, 20];
    print(items[grow_and_pick(items)]);
    print("not reached");
}
