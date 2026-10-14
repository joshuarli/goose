// runtime-debug
// A shrink receiver is resolved before its count, size and fill expressions.
// Those expressions may mutate the owner or change which owner a later call
// would select. Their output and mutations happen in source order before the
// outer operation reads the new length.
var first: i64[>..<] = [1, 2, 3];
var second: i64[>..<] = [7, 8, 9];
var use_first = true;

fn owner() -> i64[>..<]& {
    print("receiver");
    if use_first { first } else { second }
}
fn count() -> i64 {
    print("count ", first.len);
    use_first = false;
    first.push(4);
    return first.len;
}
fn size() -> i64 {
    print("size ", first.len);
    first.push(5);
    return 1;
}
fn fill() -> i64 {
    print("fill ", first.len);
    first.push(6);
    return 9;
}
fn main() {
    owner().pop_n(count());
    print("pop_n ", first.len, " ", second.len);

    use_first = true;
    owner().resize(size(), fill());
    print("resize ", first.len, " ", first[0], " ", second.len);
}
