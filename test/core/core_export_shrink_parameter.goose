fn clear_first(first: i64[>..<]&, second: i64[>..<]&) {
    let reference .= second[0];
    first.clear();
    print(reference);
}

fn main() {
    var first: i64[>..<] = [1];
    var second: i64[>..<] = [2];
    clear_first(first, second);
}
