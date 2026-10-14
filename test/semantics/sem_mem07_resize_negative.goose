// runtime-debug
fn main() {
    var values: i64[>..<] = [1, 2];
    fn size() -> i64 {
        print("size");
        return -1;
    }
    values.resize(size());
}
