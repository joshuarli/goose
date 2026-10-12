// A failed `assert` is an abort: the assertion holds twice and the program
// continues, the third check fails inside a nested call and ends the
// program with no output after it. Passing assertions print nothing of
// their own.
fn check_below(limit: i64, value: i64) {
    assert(value < limit);
    print("ok ", value);
}

fn main() {
    check_below(3, 1);
    check_below(3, 2);
    check_below(3, 3);
    print("not reached");
}
