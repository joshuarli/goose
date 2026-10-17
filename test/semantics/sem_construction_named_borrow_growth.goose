fn extend(values: i64[>..]&) {
    values.push(5);
}

fn named() -> i64[>..] {
    var result: i64[>..] = [4];
    extend(result);
    return result;
}

fn main() {
    var values = named();
    print(values[0], " ", values[1]);
}
