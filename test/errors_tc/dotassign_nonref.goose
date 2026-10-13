// error: .= rebinds references; the target has type i64
// .= rebinds references only.
fn main() {
    var x = 1;
    x .= 2;
}
