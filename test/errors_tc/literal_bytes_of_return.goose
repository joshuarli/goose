// error: returning a reference into a temporary
// bytes_of an array literal views a temporary.
fn image() -> const u8[:] { bytes_of([1, 2, 3]) }
fn main() { print(image().len); }
