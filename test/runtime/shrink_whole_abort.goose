var values: i64[>..<] = [1, 2];

fn note() -> i64 {
    print("rhs");
    return 1;
}

fn main() {
    values = [note() / 0];
    print("after");
}
