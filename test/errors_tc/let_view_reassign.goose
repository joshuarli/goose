// error: cannot assign to let view
// Only `var` makes a const u8[:] cursor movable: a let binding is never
// assigned as a whole, whatever its type.
fn main() {
    let view: const u8[:] = "abc";
    view = view[1..];
    print(view);
}
