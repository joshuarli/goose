fn grow_and_index(items: i64[>..]&) -> i64 {
    items.push(8);
    print("callee ", items.len);
    return 1;
}

fn main() {
    var items: i64[>..] = [7];
    let first .= items[0];
    items.push(9);
    first = 70;
    print(items[0], " ", items.len);

    var short: i64[>..] = [3];
    print(short[grow_and_index(short)]);
    print("unreachable");
}
