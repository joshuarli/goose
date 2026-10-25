var calls = 0;
var values: i64[..4] = [1, 2];

fn selected() -> i64[..4]& {
    calls++;
    print("receiver");
    return values;
}

fn right() -> i64 {
    print("right");
    return 1;
}

fn main() {
    let empty: i64[..4] = [];
    let full: i64[..4] = [1, 2];
    print("caps ", empty.cap, " ", full.cap);
    print("effect ", selected().cap + right(), " calls ", calls);
}
