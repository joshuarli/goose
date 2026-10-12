// error: returning a reference rooted in local, which dies with this function
// A reference parameter is in scope for the caller, but the function returns
// its own local instead of it; the parameter being present changes nothing.
fn pick(a: i64&) -> i64& {
    var local: i64 = 5;
    return local;
}

fn main() {
    var x = 1;
    let r .= pick(x);
    print(r);
}
