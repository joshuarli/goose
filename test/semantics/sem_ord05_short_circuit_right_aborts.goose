// A right side that is needed and aborts aborts the program, after the
// output of the left side. `true && (1 / zero == 1)` evaluates the division.
fn main() {
    var zero = 0;
    print("start");
    print(true && (1 / zero == 1));
    print("not reached");
}
