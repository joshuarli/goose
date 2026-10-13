// core-pilot: legacy-only
// A nonlocal result replaces an incomplete named result after intermediate scopes leave.
fn escape() {
    print("escape");
    return[71, 72],
    99 from target;
}

fn middle() {
    var scratch: i64[>..] = [201, 202];
    print("middle");
    escape();
    scratch.push(203);
}

fn build() -> i64[>..] {
    var partial: i64[>..] = [101, 102];
    print("build");
    middle();
    partial.push(103);
    return partial;
}

fn target() -> i64[>..], i64 {
    print("target");
    var result: i64[>..] = build();
    result.push(3);
    return result,
    0;
}

fn main() {
    let values,
    code = target();
    print("result ", values, " ", code);
}
