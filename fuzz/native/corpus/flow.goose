fn main() {
    var xs = [1, 2, 3];
    for x, i in xs { if x > 1 { print(i); } }
    match 1 { 0 => 2, 1..3 => 4, _ => 5 }
}
