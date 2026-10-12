var global_values: i64[>..] = [11];

fn first(values: i64[:]) -> i64 {
    return values[0];
}

fn main() {
    var local_values: i64[>..] = [22];
    print(first(global_values) + first(local_values));
}
