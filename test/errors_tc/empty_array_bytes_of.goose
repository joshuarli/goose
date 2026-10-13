// error: cannot infer the element type of []: bytes_of gives it none
// A member builtin gives its receiver no element type.
fn main() {
    print(bytes_of([]).len);
}
