// Compound assignment resolves its destination, reads the old value, and only
// then evaluates the right side, which here writes the very variable. The
// result is old value op right side, not the value the right side left
// behind. `x += bump()` with x == 1 and bump setting x to 10 and returning 2
// gives 3; reading late gives 12. The same for -= and *=.
fn main() {
    var x = 1;
    fn bump() -> i64 {
        x = 10;
        return 2;
    }
    x += bump();
    print(x);
    x = 7;
    x -= bump();
    print(x);
    x = 3;
    x *= bump();
    print(x);
}
