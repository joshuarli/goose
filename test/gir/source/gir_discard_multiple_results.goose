fn pair() -> i64, i64 {
    print("pair");
    return 1,
    2;
}

fn references(first: i64&, second: i64&) -> i64&, i64& {
    first += 1;
    return second,
    first;
}

fn main() {
    var first = 1;
    var second = 2;
    references(first, second);
    assert(first == 2 && second == 2);
    pair();
}
