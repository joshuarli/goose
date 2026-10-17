fn helper() -> bool {
    return true;
}

fn main() {
    let values: i64[1] = [11];
    print(0 < values.len && helper() && values[0] == 11);
}
