// error: cannot assign through this path (const, or a read-only instantiation, §9.5)
// A `const` parameter is read-only whatever it is given.
fn zap(s: const u8[:]) { s[0] = 65; }
fn main() {
    var text: u8[>..] = "abc";
    zap(text);
}
