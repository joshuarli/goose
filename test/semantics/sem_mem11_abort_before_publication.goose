fn first() -> i64 {
    print("rhs");
    abort("replacement stops");
}
fn main() {
    var values: i64[>..<] = [1, 2, 3];
    print("before ", values.len);
    values = [first(), 4];
    print("after ", values.len);
}
