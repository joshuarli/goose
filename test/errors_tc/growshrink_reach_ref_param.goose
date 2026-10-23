// error: storing a reference into t, which holds a grow-shrink array: such a reference lives in a variable, is passed down or returned, and is never stored (§5.2)
// t.a is read out of the caller's storage behind t, so it is rooted at t's
// class only as a bound, and so is an element of the array it leads
// to. t's argument lies in a grow-only array, but what its references lead
// to is a grow-shrink one, whose slot the pop frees and the push reuses.
//
struct Cell { v: i64 }
struct Top { a: Cell[>..<]& }
fn f(t: Top&) {
    var loc: (Cell&)[>..] = [];
    loc.push(t.a[0]);
    t.a.pop();
    t.a.push(Cell { v: 99 });
    print(loc[0].v);
}
fn main() {
    var mine: Cell[>..<] = [Cell { v: 1 }];
    var tops: Top[>..] = [];
    tops.push(Top { a: mine });
    f(tops[0]);
}
