// error: count is a variable, not a function
// A variable in scope hides the functions of its name, a global one aside.
//
import std;
fn main() {
    let xs = [1, 2, 3];
    let count = 2;
    print(count(xs) { it > 1 });
}
