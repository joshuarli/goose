fn main() {
    var values: i64[>..<] = [10, 20];
    print(values.pop());
    values.push(30);
    values.pop_n(1);
    values.resize(2, 40);
    values.clear();
    values = [7, 8];
    print(values.len, " ", values[0]);

    var bounded: i64[..3] = [1];
    let source: i64[1] = [3];
    bounded.push(3);
    bounded.append(source);
    bounded.resize(1);
    bounded.clear();
    print(bounded.len);
}
