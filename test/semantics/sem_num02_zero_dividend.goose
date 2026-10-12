// Zero as the dividend and divisors next to zero are ordinary operations:
// nothing aborts. An implementation that checks the dividend instead of the
// divisor, or treats a divisor of 1 or -1 specially, aborts or misprints.
fn quotient(a: i64, b: i64) -> i64 {
    a / b
}

fn remainder(a: i64, b: i64) -> i64 {
    a % b
}

fn uquotient(a: u8, b: u8) -> u8 {
    a / b
}

fn main() {
    print(quotient(0, 5), " ", quotient(0, -5), " ", remainder(0, 5), " ", remainder(0, -5));
    print(quotient(5, 1), " ", quotient(5, -1), " ", remainder(5, 1), " ", remainder(5, -1));
    print(uquotient(255, 255), " ", uquotient(0, 255), " ", uquotient(255, 1));
}
