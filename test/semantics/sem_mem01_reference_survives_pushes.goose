// A reference to an element of a grow-only array stays the same element
// across any number of pushes: a write through it is seen at the index, and
// a write at the index is seen through it, after 1000 pushes that would
// move the contents of any array stored in one reallocated block. The
// reference to the last element taken before the pushes is checked too.
fn main() {
    var items: i64[>..] = [1, 2, 3];
    let first .= items[0];
    let last .= items[2];
    for k in 0..1000 {
        items.push(k);
    }
    first = 100;
    items[2] = 300;
    print(items[0], " ", last, " ", items.len);
    print(first + items[1], " ", items[1002]);
}
