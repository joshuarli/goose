// error: returning a reference rooted in local, which dies with this function
// A function may not return a reference to its own local variable.
fn local_reference() -> i64& {
    var local: i64 = 5;
    return local;
}

fn main() {
    let r .= local_reference();
    print(r);
}
