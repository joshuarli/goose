fn leave() {
    return[],
    5 from outer;
}

fn trigger() -> i64 {
    leave();
    return 7;
}

fn outer() -> i64[>..], i64 {
    return[],
    trigger();
}

fn main() {
    let values,
    code = outer();
    print(values.len, " ", code);
}
