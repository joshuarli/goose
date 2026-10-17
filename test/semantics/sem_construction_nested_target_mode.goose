fn leave_inner(n: i64) {
    return[n, n + 1] from inner;
}

fn inner(n: i64) -> i64[>..] {
    leave_inner(n);
    return[0];
}

fn leave_outer(n: i64) {
    if n > 0 {
        return inner(n) from outer;
    }
}

fn outer(n: i64) -> i64[>..] {
    return[1, {
            leave_outer(n);
            0
        }];
}

fn main() {
    var values = outer(4);
    print(values[0], " ", values[1]);
}
