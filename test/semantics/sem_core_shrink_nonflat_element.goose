type ConstPair = (const i64)[2];

fn main() {
    var values: ConstPair[>..<] = [];
    values.push([1, 2]);
    print(values.len);
}
