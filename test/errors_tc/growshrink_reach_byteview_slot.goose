// error: storing a reference into t, which holds a grow-shrink array: such a reference lives in a variable, is passed down or returned, and is never stored (§5.2)
// r refers to the variable b, whose binding is the bytes of the grow-shrink
// array t.a leads to: the slice loaded through r is that byte view.
struct Cell { v: i64 }
struct Top { a: Cell[>..<]& }
struct Keep { v: const u8[:] }
fn f(t: Top&) {
    var keep: Keep[>..] = [];
    var b = t.a.bytes_of();
    let r: const (const u8[:])& = &b;
    keep.push(Keep { v: r });
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
