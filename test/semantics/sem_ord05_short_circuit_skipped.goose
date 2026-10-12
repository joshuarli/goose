// The right side of `&&` and `||` does not run when the left side decides.
// Here every right side would abort (division by zero) or write the flag;
// none of them runs, so the program completes and the flag stays false. An
// eager implementation aborts on the first line.
fn main() {
    var zero = 0;
    var written = false;
    fn write_true() -> bool {
        written = true;
        return true;
    }
    print(false && (1 / zero == 1));
    print(true || (1 / zero == 1));
    print(false && write_true());
    print(true || write_true());
    print(written);
}
