// core-construction: fixture
fn escape(n: i64) {
    if n == 1 {
        return [20, 21], 99 from descend;
    }
}

recursive fn descend(n: i64) -> i64[2], i64 {
    var scratch = n;
    print("enter ", n);
    if n == 0 { return [0, 0], 0; }
    escape(n);
    let values,
    code = descend(n - 1);
    scratch += values[0];
    print("resume ", n, " ", values[0], " ", values[1], " ", code, " ", scratch);
    return values, code;
}

fn main() {
    let values,
    code = descend(3);
    print("result ", values[0], " ", values[1], " ", code);
}
