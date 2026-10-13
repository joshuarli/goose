// error: array fill count K names a local variable, not a constant
// An appended literal's fill count is checked as any other's.
fn main() {
    let K = 5;
    var a: i64[>..] = [];
    a.append([1; K]);
    print(a.len);
}
