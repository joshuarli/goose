fn returns() {}

fn main() {
    var values: i64[>..] = [returns()];
    print(values.len);
}
