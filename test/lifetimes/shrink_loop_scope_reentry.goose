fn main() {
    var values: i64[>..<] = [11, 22, 33];
    for i in 3 {
        if i == 0 {
            let first = &values[0];
            print(first);
        } else {
            values.pop();
        }
    }
    print(values);
}
