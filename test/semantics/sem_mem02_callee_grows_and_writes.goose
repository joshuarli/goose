// The callee both grows the array and writes the held element. Growth never
// invalidates the caller's reference: after the call it still designates
// element 0, now holding the callee's value, and the new elements are
// beyond it.
fn grow_and_overwrite(items: i64[>..]&) {
    for k in 0..200 {
        items.push(k);
    }
    items[0] = -1;
}

fn main() {
    var items: i64[>..] = [4];
    let held .= items[0];
    grow_and_overwrite(items);
    held -= 1;
    print(held, " ", items[0], " ", items.len, " ", items[200]);
}
