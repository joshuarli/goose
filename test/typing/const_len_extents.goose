// A `let` or `const` global's `.len`, and `.cap`, is a constant a size,
// capacity or fill count may use where its declaration fixes it (§3.3): by
// its written fixed or limited array type, or by the array, fill or string
// literal, or other such global, it is initialized to. Elsewhere it is an
// i64 like any other `.len`.
const table = [10, 20, 30, 40];
let typed: i64[3] = [1, 2, 3];
let room: i64[..6] = [1];
let filled = [0; typed.len + 2];
let name = "goose";
let copied = typed;
let twice = table.len * 2;
const words = ["a", "bc", "def"];

struct Row { cells: i64[table.len], spare: i64[..room.cap] }
struct Pair<T> { a: T[words.len], b: T[..copied.len] }

fn total(xs: i64[table.len]) -> i64 {
    var s = 0;
    for x in xs { s += x; }
    return s;
}

// Its written type fixes typed's length, which no reference can change.
fn bump(r: i64[3]&) { r[0] += 10; }

fn main() {
    bump(typed);
    let a: i64[typed.len] = [7, 8, 9];
    var b: i64[..table.len + room.cap] = [];
    b.push(1);
    let c = [5; filled.len];
    let d: u8[name.len] = "geese";
    let e: i64[twice] = [0, 0, 0, 0, 0, 0, 0, 0];
    var counts: i64[words.len] = [0, 0, 0];
    counts[2] += 1;
    let row = Row { [1, 2, 3, 4], [5] };
    let pair = Pair<i64> { [1, 2, 3], [4] };
    let four: i64 = 4;
    let m = match four { twice => "twice", 4 => "four", _ => "other" };
    print(a, " ", b.cap, " ", c, " ", d, " ", e.len, " ", counts);
    print(row, " ", row.spare.cap, " ", pair, " ", pair.b.cap, " ", m);
    print(total(table), " ", typed, " ", table.len + copied.len);
}
