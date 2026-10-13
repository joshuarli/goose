fn main() {
    let values: i64[>..] = [1];
    let source: i64[1] = [3];
    fn add_values() {
        values.push(2);
        values.append(source);
    }
    add_values();
    print(values.len, " ", values[2]);
}
