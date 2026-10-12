// error: returning a reference rooted in local, which dies with this function
// Nor may it return a slice of its own local array.
fn local_slice() -> i64[:] {
    var local: i64[3] = [1, 2, 3];
    return local[0..2];
}

fn main() {
    let s = local_slice();
    print(s.len);
}
