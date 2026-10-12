// A variable declared in a loop body is a new variable on each iteration,
// initialized again every time, whether the iteration ends by falling
// through, by `continue` or by `break`. Here `fresh` restarts from 100 every
// iteration while `kept` accumulates. A wrong implementation that gives the
// body one storage slot and skips the reinitialization prints 100, 101, 102
// for the first column.
fn main() {
    var kept = 0;
    for i in 0..5 {
        var fresh = 100;
        fresh += i;
        kept += fresh;
        if i == 1 {
            continue;
        }
        print(fresh, " ", kept);
        if i == 3 {
            break;
        }
    }
    var n = 0;
    while n < 3 {
        let square = n * n;
        n += 1;
        print(square);
    }
}
