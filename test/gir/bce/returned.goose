fn read() -> i64 {
    let values: i64[1] = [11];
    if 0 < values.len && values[0] == 11 {
        return 7;
    }
    return 9;
}

fn main() {
    print(read());
}
