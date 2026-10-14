// runtime-debug
fn main() {
    var values: i64[>..<] = [1, 2];
    fn fill() -> i64 {
        values[0] += 1;
        print("fill");
        return 9;
    }
    values.resize(values.len, fill());
    print(values.len, " ", values[0], " ", values[1]);
}
