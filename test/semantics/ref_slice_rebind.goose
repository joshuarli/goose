fn replace(p: i64[:]&, replacement: i64[:]) {
    p = replacement;
}

fn main() {
    var values: i64[>..] = [10, 20];
    var view = values[0..1];
    replace(view, values[1..2]);
    print(view[0]);
}
