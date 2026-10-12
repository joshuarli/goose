// error: storing a reference rooted at inner, which does not outlive the destination
// The same rule for a slice: a view of an inner block's array may not be
// stored in a slice variable of the outer scope.
fn main() {
    var items: i64[>..] = [1, 2, 3];
    var kept: i64[:] = items[0..1];
    {
        var inner: i64[>..] = [4, 5];
        kept = inner[0..2];
    }
    print(kept[0]);
}
