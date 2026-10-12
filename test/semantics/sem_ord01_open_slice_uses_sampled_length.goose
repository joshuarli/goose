// An omitted upper bound means the sampled length, not the length after the
// lower bound expression has grown the array. The lower bound pushes three
// elements and returns 1, yet the slice covers only the original 4 elements
// from position 1: three of them. A later slice of the array sees all 7.
fn grow_and_start(items: i64[>..]&) -> i64 {
    items.push(5);
    items.push(6);
    items.push(7);
    return 1;
}

fn main() {
    var items: i64[>..] = [1, 2, 3, 4];
    let first = items[grow_and_start(items)..];
    print(first.len, " ", first[0], " ", first[2]);
    let second = items[1..];
    print(second.len, " ", second[5]);
}
