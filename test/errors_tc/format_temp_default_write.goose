// error: cannot write through this reference: non-writable provenance
// default<i64>() is a value built in a temporary, as a literal is: a
// format overload taking it by reference is given that temporary, read-only,
// as a literal's.
fn format(out: u8[>..]&, v: i64&) { v = 9; out.append("x"); }
fn main() {
    print(default<i64>());
}
