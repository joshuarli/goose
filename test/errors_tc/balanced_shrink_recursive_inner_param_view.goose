// error: cannot call a: it shrinks G while s is still used, and s may refer into G
// b's call back into the cycle applies b's record once a round has made it:
// the pair for the view of a parameter's class live across the
// call reaches a, whose caller passes G's view.
var G: i64[>..<] = [1, 2, 3];
recursive fn a(s: i64[:], d: i64) -> i64 {
    var t = 0;
    if d < 3 { t = b(s, d); }
    if d == 3 {
        G.clear();
        G.push(77);
    }
    return t + d;
}
recursive fn b(s: i64[:], d: i64) -> i64 {
    let t = a(s, d + 1);
    return t + s[0];
}
fn main() {
    print(a(G[..], 1));
}
