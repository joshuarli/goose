// error: array elements may not be resizable: i64[>..]
// Array elements may not be resizable.
fn main() {
    var a: i64[>..][] = [];
    print(a.len);
}
