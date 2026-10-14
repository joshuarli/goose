// runtime-debug
fn shrink_first(first: i64[>..<]&, second: i64[>..<]&) {
    first.pop();
    print(second[1]);
}

fn main() {
    var first: i64[>..<] = [10, 11];
    var second: i64[>..<] = [20, 21];
    let held = &second[1];
    shrink_first(first, second);
    print(held, " ", first.len, " ", second.len);
}
