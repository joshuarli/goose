// error: cannot call helper, which shrinks s while v is still used: it may hold a reference or slice into it
// Only grow-shrink arrays have balanced calls: a grow-only array's
// shrinks are checked at every call as before.
fn helper(s: i64[>..]&) {
    let mark = s.len;
    s.push(4);
    s.resize(mark);
}
fn main() {
    var s: i64[>..] = [9];
    let v = s[..];
    helper(s);
    print(v[0]);
}
