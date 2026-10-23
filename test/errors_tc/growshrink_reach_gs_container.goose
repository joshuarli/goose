// error: storing a reference into t, which holds a grow-shrink array: such a reference lives in a variable, is passed down or returned, and is never stored (§5.2)
// t's argument lies in a grow-shrink array of Tops, which cannot hold a
// Cell; the Cell t.a[0] names lies in the one t.a leads to.
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
    var tops: Top[>..<] = [];
    tops.push(Top { a: mine });
    f(tops[0]);
}
