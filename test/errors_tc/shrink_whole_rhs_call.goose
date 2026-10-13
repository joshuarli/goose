// error: cannot call current_length in the value assigned to values
fn main() {
    var values: i64[>..<] = [1, 2];
    fn current_length() -> i64 {
        return values.len;
    }
    values = [current_length()];
}
