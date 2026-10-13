var first: i64[>..<] = [1];
var second: i64[>..<] = [2];

fn clear_first(a: i64[>..<]&, b: i64[>..<]&) {
    let reference .= b[0];
    a.clear();
    print(reference);
}

fn main() {
    clear_first(first, second);
}
