fn main() {
    let limited: i64[..4] = [5, 6];
    fn write_element() { limited[0] = 7; }
    print(limited[0]);
    write_element();
    print(limited[0]);
}
