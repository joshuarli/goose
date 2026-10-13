// error: cannot assign to let x
// `const x = e` is a let of a const type: the binding is not
// reassigned, where a var of that type would be.
fn main() {
    const x = "a";
    x = "b";
    print(x);
}
