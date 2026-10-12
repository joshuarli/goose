// error: storing a reference rooted at y, which does not outlive the destination
// A call that returns its parameter passes the argument's root on: the result
// is rooted at the inner variable, which the outer reference may not keep.
fn pass(a: i64&) -> i64& {
    return a;
}

fn main() {
    var x = 4;
    var r .= pass(x);
    {
        var y = 5;
        r .= pass(y);
    }
    print(r);
}
