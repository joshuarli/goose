fn main() {
    var values: i64[>..<] = [10, 20];
    var run = values[..];
    values.pop();
    run = values[..];
    print(run.len);
}
