// The view's scope ends before the shrink. Each loop iteration creates a
// fresh view whose use does not survive into the backedge.
fn main() {
    var values: i64[>..<] = [1, 2, 3];
    var seen = 0;
    for round in 2 {
        {
            let view = values[..];
            seen += view[0];
        }
        values.pop();
        values.push(10 + round);
    }
    print(seen, " ", values.len, " ", values[0], " ", values[1], " ", values[2]);
}
