recursive fn consume(values: i64[>..<]&, reference: i64&, count: i64) {
    if count == 0 {
        print(reference);
        values.clear();
    } else {
        consume(values, reference, count - 1);
    }
}

fn main() {
    var values: i64[>..<] = [1];
    consume(values, values[0], 1);
}
