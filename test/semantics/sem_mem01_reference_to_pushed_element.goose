// A reference taken to the element a push just added designates that
// element when more are pushed after it: the array's earlier elements keep
// their values, the referenced one is rewritten in place, and the length
// counts every push. Pushing from an empty array makes the first element.
fn main() {
    var items: i64[>..] = [];
    items.push(7);
    let seven .= items[0];
    items.push(8);
    items.push(9);
    seven = 70;
    print(items[0], " ", items[1], " ", items[2], " ", items.len);
    let nine .= items[2];
    for k in 0..64 {
        items.push(k);
    }
    nine += 1;
    print(items[2], " ", nine, " ", items.len);
}
