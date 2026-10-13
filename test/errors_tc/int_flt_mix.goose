// error: expected a value of type i64, got f64 (a float converts to an integer only with an explicit `as`)
// An integer mixed with a float is a float, which converts back to an
// integer only with an explicit `as`.
fn main() {
    var integer: i64 = 1;
    var floating: f64 = 2.0;
    integer = integer + floating;
    print(integer);
}
