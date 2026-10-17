fn helper() -> i64 {
    print(7);
    return 9;
}

fn main() {
    let values: i64[1] = [11];
    print(0 < values.len && values[0] == 11);
    print(helper());
}
