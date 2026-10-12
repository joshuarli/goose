// The same sampling rule for slice bounds: the upper bound expression grows
// the array and returns 3, valid only in the grown array of length 3. The
// bounds are checked against the sampled length 2 and the slice aborts.
fn grow_and_bound(items: i64[>..]&) -> i64 {
    items.push(30);
    return 3;
}

fn main() {
    var items: i64[>..] = [10, 20];
    let window = items[0..grow_and_bound(items)];
    print(window.len);
}
