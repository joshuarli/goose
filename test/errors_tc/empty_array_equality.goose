// error: cannot infer the element type of []: == gives it none
// An operand of == takes no type from the other one, so neither [] has an
// element type to compare by.
fn main() {
    print([] == []);
}
