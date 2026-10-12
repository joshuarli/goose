// The index expression of `items[...]` grows `items`. The bounds check
// uses the length sampled before the index ran (3), and the index 2 is in
// it; the element read is the original one, and the grown length is seen
// afterwards. The check must neither fail nor read a moved element.
fn grow_and_pick(items: i64[>..]&) -> i64 {
    items.push(40);
    print("pushed, length ", items.len);
    return 2;
}

fn main() {
    var items: i64[>..] = [10, 20, 30];
    print(items[grow_and_pick(items)]);
    print(items.len, " ", items[3]);
}
