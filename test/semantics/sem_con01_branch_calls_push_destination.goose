// Each branch builds a variable-size array directly into a pushed element.
// The nested calls and their side effects run once for each selected branch.
var calls = 0;

fn leaf(n: i64) -> i64[] {
    calls++;
    return [n, n + 1];
}

fn relay(n: i64) -> i64[] {
    calls++;
    return leaf(n);
}

fn main() {
    var rows: i64[][>..] = [];
    for i in 2 {
        rows.push(if i == 0 { relay(10) } else { relay(20) });
    }
    print(rows, " ", calls);
}
