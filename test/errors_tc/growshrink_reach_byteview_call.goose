// error: storing a reference into t, which holds a grow-shrink array: such a reference lives in a variable, is passed down or returned, and is never stored (§5.2)
// same hands back the byte view it was given, which no slot has held: the
// bytes of the grow-shrink array t.a leads to.
struct Cell { v: i64 }
struct Top { a: Cell[>..<]& }
struct Keep { v: const u8[:] }
fn same(s: const u8[:]) -> const u8[:] { s }
fn f(t: Top&) {
    var keep: Keep[>..] = [];
    keep.push(Keep { v: same(t.a.bytes_of()) });
    t.a.clear();
    t.a.push(Cell { v: 99 });
    print(keep[0].v);
}
fn main() {
    var mine: Cell[>..<] = [Cell { v: 1 }];
    var tops: Top[>..] = [];
    tops.push(Top { a: mine });
    f(tops[0]);
}
