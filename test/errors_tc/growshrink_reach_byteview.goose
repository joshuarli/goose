// error: storing a reference into t, which holds a grow-shrink array: such a reference lives in a variable, is passed down or returned, and is never stored (§5.2)
// The bytes of the array t.a leads to are a grow-shrink array's elements,
// which the clear frees and the push reuses.
struct Cell { v: i64 }
struct Top { a: Cell[>..<]& }
struct Keep { v: const u8[:] }
fn f(t: Top&) {
    var keep: Keep[>..] = [];
    keep.push(Keep { v: t.a.bytes_of() });
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
