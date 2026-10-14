// runtime-debug
fn main() {
    var values: i64[>..<] = [1];
    fn size() -> i64 {
        print("size");
        return 2;
    }
    values.resize(size());
}
