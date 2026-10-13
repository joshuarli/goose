// core-pilot: legacy-only
// Copying a different array is safe while the destination is being replaced.
fn main() {
    var source: i64[>..] = [2, 3];
    var destination: i64[>..] = [1];
    destination = copy(source);
    print("destination ", destination, " source ", source);
}
