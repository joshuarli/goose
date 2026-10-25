fn main() {
    var values: i64[2] = [10, 20];
    var reference = &values[0];
    fn read() -> i64 {
        reference
    }
    print(read());
    reference .= &values[1];
    print(read());
}
