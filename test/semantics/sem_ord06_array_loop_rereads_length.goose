// A loop over a growable array tests the current length before each
// iteration, so elements pushed by the body are visited. The body pushes
// until the array holds six elements; the loop visits all six (sum 21), and
// the index of the last one is 5. An implementation that fixes the length at
// loop entry visits only the first.
fn main() {
    var items: i64[>..] = [1];
    var sum = 0;
    var last = 0;
    for x,
    i in items {
        if items.len < 6 {
            items.push(x + 1);
        }
        sum += x;
        last = i;
    }
    print(sum, " ", last, " ", items.len);
}
