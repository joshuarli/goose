// error: constant integer expression expected for array size
// A size names a `let` or `const` global, never a `var` (§3.3, §11.1).
var table = [1, 2, 3];

fn main() {
    let a: i64[table.len] = [1, 2, 3];
    print(a, table);
}
