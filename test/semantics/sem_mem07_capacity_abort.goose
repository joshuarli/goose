// A limited-array push beyond capacity aborts before appending an element.
fn main() {
    var xs: i64[..1] = [7];
    print(xs.len, " ", xs[0]);
    xs.push(8);
    print("unreachable");
}
