// core-pilot: legacy-only
// Nested calls and selected branches construct variable-size arrays directly
// into push, append, argument, and whole-assignment destinations.
var calls = 0;

fn leaf(n: i64) -> i64[] {
    calls++;
    return [n, n + 1];
}

fn relay(n: i64) -> i64[] {
    calls++;
    return leaf(n);
}

fn use(values: i64[]) {
    print("argument ", values);
}

fn main() {
    var rows: i64[][>..] = [];
    for i in 2 {
        rows.push(if i == 0 { relay(10) } else { relay(20) });
    }
    print("push ", rows, " calls ", calls);

    var appended: i64[>..] = [0];
    appended.append(if true { relay(30) } else { relay(31) });
    print("append ", appended, " calls ", calls);

    use(if false { relay(40) } else { relay(50) });
    print("argument calls ", calls);

    var assigned: i64[>..] = [99];
    assigned = if true { relay(60) } else { relay(70) };
    print("assignment ", assigned, " calls ", calls);
}
