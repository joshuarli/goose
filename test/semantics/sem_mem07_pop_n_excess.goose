// runtime-debug
fn main() {
    var values: i64[>..<] = [1, 2];
    fn count() -> i64 {
        print("count");
        return 3;
    }
    values.pop_n(count());
}
