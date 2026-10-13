fn balanced(values: i64[>..<]&) {
    let mark = values.len;
    values.push(9);
    values.resize(mark);
}

fn main() {
    var values: i64[>..<] = [1];
    let reference .= values[0];
    balanced(values);
    print(reference);
}
