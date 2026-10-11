struct Pair { left: i64, right: i64 }

fn add(a: i64&, b: i64&) {
    a += 1;
    b += a;
}

fn main() {
    var pair = Pair { left: 2, right: 3 };
    add(pair.left, pair.left);
    add(pair.left, pair.right);
    print(pair.left, " ", pair.right);
}
