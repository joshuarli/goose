fn main() {
    let values: i64[>..] = [10, 20];
    fn show_values() { print(values.len, " ", values[0]); }
    show_values();
}
