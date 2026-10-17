// core-pilot: legacy-only
struct Pair<T> {
    first: T,
    second: T
}

fn make_values(n: i64) -> i64[>..], i64 {
    var values: i64[>..] = [n, n + 1];
    return values,
    n + 2;
}

fn size(values: i64[>..]) -> i64 {
    return values.len;
}

fn numbers(n: i64) -> i64[>..] {
    var values: i64[>..] = [n, n + 1];
    return values;
}

fn main() {
    let pair = Pair < i64 > {
        first: 3,
        second: 4
    };
    var all: i64[>..] = [4, 5];
    let values,
    next = make_values(7);
    let saved: i64[>..] = numbers(3);
    print(pair.first, " ", size(copy(values)), " ", next);
    append(all, copy(values));
    append(all, numbers(8));
    print(saved.len, " ", all.len);
}
