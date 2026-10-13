// error: storing a reference rooted at buf, which does not outlive the destination
// Elements appended out of a slice are read out of the storage it views:
// the slices they hold point into buf, which ends first.
fn main() {
    var words: u8[:][>..] = [];
    {
        var buf: u8[>..] = [];
        buf.append("ab cd");
        var parts: u8[:][>..] = [];
        parts.push(buf[0..2]);
        parts.push(buf[3..5]);
        words.append(parts[..]);
    }
    print(words.len);
}
