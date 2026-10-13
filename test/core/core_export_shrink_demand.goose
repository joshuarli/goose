fn consume(values: i64[>..<]&, reference: i64&) {
    print(reference);
    values.clear();
}

fn main() {
    var values: i64[>..<] = [1];
    consume(values, values[0]);
}
