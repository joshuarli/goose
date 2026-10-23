// error: storing a reference into mine, which holds a grow-shrink array: such a reference lives in a variable, is passed down or returned, and is never stored (§5.2)
// first's result is rooted at its argument's root, tops, only as a bound: it
// was read out of the storage behind t. tops holds none, but its references
// lead to mine, whose slot the pop frees and the push reuses.
struct Cell { v: i64 }
struct Top { a: Cell[>..<]& }
fn first(t: Top&) -> Cell& { t.a[0] }
fn main() {
    var mine: Cell[>..<] = [Cell { v: 1 }];
    var tops: Top[>..] = [];
    tops.push(Top { a: mine });
    var loc: (Cell&)[>..] = [];
    loc.push(first(tops[0]));
    mine.pop();
    mine.push(Cell { v: 99 });
    print(loc[0].v);
}
