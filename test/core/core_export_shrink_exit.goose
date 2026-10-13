fn main() {
    var values: i64[>..<] = [1];
    let reference .= values[0];
    while true {
        print(reference);
        values.clear();
        break;
    }
}
