// error: storing a reference rooted at x, which does not outlive the destination
// The elements of an appended literal are stored in the receiver, so
// a reference in one must outlive it.
fn main() {
    var refs: (i64&)[>..] = [];
    {
        let x = 5;
        refs.append([x]);
    }
    print(refs.len);
}
