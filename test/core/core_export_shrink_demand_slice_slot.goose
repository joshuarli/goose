fn consume(values: i64[>..<]&, view: i64[:]&) {
    print(view[0]);
    values.clear();
}

fn main() {
    var values: i64[>..<] = [1];
    var view: i64[:] = values[..];
    consume(values, view);
}
