// runtime-debug
var values: i64[..4] = [];

fn selected() -> i64[..4]& {
    print("receiver");
    abort("receiver failed");
    return values;
}

fn right() -> i64 {
    print("right");
    return 1;
}

fn main() {
    let value = selected().cap + right();
    print(value);
}
