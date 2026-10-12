// A slice keeps its own length: growing the array it views does not extend
// the loop over the slice. The slice covers two elements; the body pushes two
// more onto the array, and only the two original elements are visited. The
// array itself grows by four in total (the pushes happen once per
// iteration, and the slice loop runs twice).
fn main() {
    var items: i64[>..] = [1, 2];
    let window = items[0..2];
    var visited = 0;
    for x in window {
        items.push(x * 10);
        items.push(x * 100);
        visited += 1;
    }
    print(visited, " ", items.len, " ", items[2], " ", items[5]);
}
