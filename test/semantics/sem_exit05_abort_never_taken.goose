// An abort on a branch that is never taken, and an assertion that always
// holds, change nothing: the program runs to its end and exits normally. An
// implementation that aborts when it merely reaches the statement's block, or
// that evaluates the message eagerly, fails here.
fn main() {
    var total = 0;
    for i in 0..4 {
        assert(i < 4);
        if i > 10 {
            abort("impossible");
        }
        total += i;
    }
    print(total);
}
