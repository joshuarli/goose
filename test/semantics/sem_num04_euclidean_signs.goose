// runtime-debug
// The remainder is Euclidean at every sign combination: the result lies in
// [0, |b|) and is never negative, while the quotient truncates toward zero.
// C's truncating remainder gives -2 for -5 % 3 where this program prints 1;
// a flooring division gives -4 for -7 / 2 where this prints -3. The debug
// build must agree (the first line asks for it).
fn quotient(a: i64, b: i64) -> i64 {
    a / b
}

fn remainder(a: i64, b: i64) -> i64 {
    a % b
}

fn remainder8(a: i8, b: i8) -> i8 {
    a % b
}

fn main() {
    print(remainder(5, 3), " ", remainder(-5, 3), " ", remainder(5, -3), " ", remainder(-5, -3));
    print(remainder(6, 3), " ", remainder(-6, 3), " ", remainder(-1, 3), " ", remainder(-3, 3));
    print(quotient(7, 2), " ", quotient(-7, 2), " ", quotient(7, -2), " ", quotient(-7, -2));
    print(remainder(7, 2), " ", remainder(-7, 2), " ", remainder(7, -2), " ", remainder(-7, -2));
    print(remainder8(-7, 4), " ", remainder8(-1, 127), " ", remainder8(-128, 127));
}
