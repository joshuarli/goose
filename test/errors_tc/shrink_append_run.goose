// error: cannot call shrink, which shrinks values: the elements of values, which the statement reads after it
fn shrink(a: i64[>..<]&) -> i64 {
    a.pop();
    return a.len;
}

fn main() {
    var values: i64[>..<] = [1, 2, 3];
    var out: i64[>..] = [];
    out.append(values[..shrink(values)]);
}
