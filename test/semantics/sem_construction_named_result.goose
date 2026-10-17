fn named(n: i64) -> i64[>..] {
    var result: i64[>..] = [n];
    result.push(n + 1);
    return result;
}

fn main() {
    var values = named(4);
    print(values[0], " ", values[1]);
}
