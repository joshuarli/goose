// error: cannot infer the element type of []: a for loop gives it none
// A loop over a [] gives it no element type for its binder.
fn main() {
    for x in [] { }
    print(1);
}
