// runtime-debug
fn main() {
    var values: i64[..2] = [1];
    fn size() -> i64 {
        print("size");
        return 3;
    }
    fn fill() -> i64 {
        print("fill");
        return 9;
    }
    values.resize(size(), fill());
}
