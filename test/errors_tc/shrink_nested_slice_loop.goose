// error: cannot pop values
fn main() {
    var values: i64[>..<] = [1, 2, 3];
    for outer in 2 {
        for value in values[..] {
            values.pop();
            print(outer, " ", value);
        }
    }
}
