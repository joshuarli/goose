// error: storing a reference into t, which holds a grow-shrink array: such a reference lives in a variable, is passed down or returned, and is never stored (§5.2)
// A by-value holder parameter's references point into the caller's storage
// behind its class, which bounds t.a and an element of the array it
// leads to: a grow-shrink array, whose slot the pop frees and the push
// reuses.
struct Cell { v: i64 }
struct Top { a: Cell[>..<]& }
fn f(t: Top) {
    var loc: (Cell&)[>..] = [];
    loc.push(t.a[0]);
    t.a.pop();
    t.a.push(Cell { v: 99 });
    print(loc[0].v);
}
fn pass(ts: Top[>..]&) { f(ts[0]); }
fn main() {
    var mine: Cell[>..<] = [Cell { v: 1 }];
    var tops: Top[>..] = [];
    tops.push(Top { a: mine });
    pass(tops);
}
