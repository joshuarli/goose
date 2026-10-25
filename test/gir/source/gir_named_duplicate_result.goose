fn pair() -> i64[>..], i64[>..] {
    var values: i64[>..] = [14, 15];
    return values,
    values;
}

fn main() {
    let first,
    second = pair();
    first[0] = 99;
    print(first, " ", second);
}
