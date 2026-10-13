// error: enum S has payloads holding self-relative references
// S links to variable-mode S's, but an array of fixed-mode ones would hold
// payloads that bind only by value, which loses the links.
enum S { Nil, Cons { v: i64, next: S..&<u32>? } }
fn main() {
    var ss: S[>..] = [];
    ss.push(S.Nil);
    print(ss.len);
}
