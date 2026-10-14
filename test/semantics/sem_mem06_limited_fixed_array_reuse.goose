// runtime-debug
fn main() {
    var rows: i64[2][..4] = [[1, 2], [3, 4]];
    let saved = &rows[1][0];
    rows.pop_n(1);
    print("saved ", saved);
    rows.push([5, 6]);
    print("saved ", saved);
    rows.pop();
    print("saved ", saved);
    rows.resize(2, [7, 8]);
    print("saved ", saved);
    rows.resize(1);
    print("saved ", saved);
    rows.clear();
    print("saved ", saved);
    rows.push([11, 12]);
    let suffix: i64[2][1] = [[13, 14]];
    rows.append(suffix);
    print("saved ", saved, " ", rows.len, " ", rows[0][0], " ", rows[1][0]);
}
