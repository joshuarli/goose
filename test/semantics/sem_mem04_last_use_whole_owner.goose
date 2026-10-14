// runtime-debug
fn main() {
    var values: i64[>..<] = [10, 20];
    let view = values[..];
    let owner = values;
    print(view[1]);
    values.pop();
    print(owner.len, " ", owner[0]);
}
