// runtime-debug
fn main() {
    var values: i64[..1] = [7];
    fn element() -> i64 {
        print("element");
        return 8;
    }
    values.push(element());
}
