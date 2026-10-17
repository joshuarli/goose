fn produce(n: i64) -> i64[>..] {
    return[n, n + 1];
}

fn leave(n: i64) {
    return produce(n) from target;
}

fn target(n: i64) -> i64[>..] {
    leave(n);
    return[0];
}

fn main() {
    var values = target(4);
    print(values[0], " ", values[1]);
}
