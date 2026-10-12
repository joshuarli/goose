// The language text (section 3.7) says print evaluates and renders its
// arguments in order, "each just before its text", and also that the line is
// written "as one write". The two readings differ when evaluating a later
// argument writes output of its own: written eagerly, "a" would precede the
// callee's line; written as one line after all arguments, the callee's line
// comes first.
fn inner() -> i64 {
    print("inner");
    return 5;
}

fn main() {
    print("a", inner(), "b");
}
