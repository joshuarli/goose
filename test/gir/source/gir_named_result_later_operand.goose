fn pair() -> i64[>..], i64[>..] {
    var values: i64[>..] = [1, 2];
    return values,
    {
        values.clear();
        values.push(3);
        [9]
    };
}

fn main() {
    let first,
    second = pair();
    print(first, " ", second);
}
