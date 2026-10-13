fn main() {
    let limited: i64[..4] = [5, 6];
    fn write_element() { limited[0] = 7; }
    write_element();
}
