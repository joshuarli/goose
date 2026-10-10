// error: table is bound to a writable reference here, through which it may change, while the array size at
// error: const_len_written_before.goose:9 relies on it keeping its initializer's value
// §3.3, §11.1: either order is an error, as for a named constant.
let table = [1, 2, 3];

fn bump(r: i64[3]&) { r[0] += 10; }

fn main() {
    let a: i64[table.len] = [0, 0, 0];
    bump(table);
    print(a, table);
}
