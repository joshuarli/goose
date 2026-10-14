// The indexed value is copied before pop. It remains usable after the owner
// releases its element storage because the local holds no interior reference.
fn main() {
    var values: i64[>..<] = [10, 20, 30];
    let saved = values[1];
    values.pop_n(3);
    print(saved, " ", values.len);
}
