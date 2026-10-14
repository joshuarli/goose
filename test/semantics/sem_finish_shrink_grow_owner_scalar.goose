fn main() {
    var values: i64[>..] = [3, 5, 8];
    print(values.pop(), " ", values.len);
    values.resize(1);
    print(values[0]);
    values.clear();
    print(values.len);
}
