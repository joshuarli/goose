fn calc(x: i64) -> i64 {
    var total = 0;
    for i in 0..x {
        total += i * 3 + 1;
    }
    return total;
}

fn main() {
    print(calc(97));
}
