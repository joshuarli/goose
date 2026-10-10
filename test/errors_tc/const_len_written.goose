// error: the array size relies on table keeping its initializer's value, but a writable reference bound to table at
// error: const_len_written.goose:11 may change it
// §3.3, §11.1: table's length is its initializer's, which a size takes as it
// does a named constant's value, so table may not also be bound to a
// writable reference (writing its type, i64[3], would fix the length).
let table = [1, 2, 3];

fn bump(r: i64[3]&) { r[0] += 10; }

fn main() {
    bump(table);
    let a: i64[table.len] = [0, 0, 0];
    print(a, table);
}
