// A slice of a grow-only array keeps its start and its length of 2 when the
// array grows underneath it, and keeps viewing the same elements: a write
// through the array is visible in the slice, and a write through the slice in
// the array. An implementation that copies the viewed run at creation sees
// neither write.
fn main() {
    var items: i64[>..] = [5, 6, 7, 8];
    var window = items[1..3];
    for k in 0..500 {
        items.push(k);
    }
    items[1] = 60;
    window[1] = 70;
    print(window.len, " ", window[0], " ", window[1]);
    print(items[1], " ", items[2], " ", items.len);
}
