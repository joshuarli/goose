fn balanced(values: i64[>..<]&) {
    let mark = values.len;
    values.push(9);
    values.resize(mark);
}

fn main() {
    var values: i64[>..<] = [1];
    let reference .= values[0];
    print(reference);
    values.clear();

    var first: i64[>..<] = [1];
    var second: i64[>..<] = [2];
    let other .= second[0];
    first.clear();
    print(other);

    balanced(second);
    print(second.len);

    var limited: i64[..2] = [3];
    let kept .= limited[0];
    limited.clear();
    print(kept);
    return;
    print(reference);
}
