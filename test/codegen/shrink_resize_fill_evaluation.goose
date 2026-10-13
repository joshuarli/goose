var fill_calls = 0;

fn fill() -> i64 {
    fill_calls += 1;
    print("fill ", fill_calls);
    return 9;
}

fn main() {
    var values: i64[>..<] = [1, 2, 3];
    values.resize(1, fill());
    print(values);

    values.resize(1, fill());
    print(values);
}
