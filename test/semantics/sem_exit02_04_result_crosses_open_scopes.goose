// core-pilot: legacy-only
// The two intermediate calls own live arrays when the deepest helper
// returns a nonfixed value from target. Their scopes are removed while the
// value is delivered into target's result destination.
fn leave(n: i64) {
    return [n, n + 1] from target;
}

fn inner(n: i64) {
    var scratch: i64[>..] = [101, 102];
    print("inner");
    leave(n);
    scratch.push(103);
}

fn middle(n: i64) {
    var scratch: i64[>..] = [201, 202];
    print("middle");
    inner(n);
    scratch.push(203);
}

fn target(n: i64) -> i64[>..] {
    var result: i64[>..] = [1];
    print("target");
    middle(n);
    result.push(2);
    return result;
}

fn main() {
    var result = target(40);
    result.push(99);
    print(result);
}
