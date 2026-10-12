// A by-value argument is read when it is evaluated, before a later argument
// runs; a reference argument designates the variable, so the callee reads
// whatever it holds when the callee runs. `change` sets the shared variable
// to 10 and yields 2. By value: the first argument stays 1. By reference:
// the first argument is 10. An implementation that evaluates arguments right
// to left or reads the variable late prints "10 2" for the first line.
fn by_value(a: i64, b: i64) {
    print("value ", a, " ", b);
}

fn by_reference(a: i64&, b: i64) {
    print("reference ", a, " ", b);
}

fn main() {
    var shared = 1;
    fn change() -> i64 {
        shared = 10;
        return 2;
    }
    by_value(shared, change());
    shared = 1;
    by_reference(shared, change());
}
