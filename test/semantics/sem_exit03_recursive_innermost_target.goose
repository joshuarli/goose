// core-pilot: legacy-only
// The helper exits from the innermost active descend call. Its caller and
// the next outer activation resume and use their own still-live locals.
fn leave(n: i64) {
    if n == 1 {
        print("escape ", n);
        return 20 from descend;
    }
}

recursive fn descend(n: i64) -> i64 {
    var scratch = n;
    print("enter ", n);
    if n == 0 { return 0; }
    leave(n);
    let child = descend(n - 1);
    scratch += child;
    print("resume ", n, " ", child, " ", scratch);
    return child + 1;
}

fn main() {
    print("result ", descend(3));
}
