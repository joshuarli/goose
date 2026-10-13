// core-pilot: legacy-only
// Named results retain mutations, independent returns stay fresh, and repeated channels are independent.
// warning: another return hands back `first`
// warning: another return's value may read or write it
var fresh_calls = 0;

fn named_mutated() -> i64[] {
    var values: i64[>..] = [1];
    values.push(2);
    return values;
}

fn fresh(n: i64) -> i64[] {
    fresh_calls++;
    return[n, n + 1];
}

fn independent_return(choose_fresh: bool) -> i64[] {
    var values: i64[>..] = [3];
    values.push(4);
    if choose_fresh {
        return fresh(8);
    }
    values.push(5);
    return values;
}

fn different_locals(choose_second: bool) -> i64[] {
    var first: i64[>..] = [10];
    var second: i64[>..] = [20];
    if choose_second {
        return second;
    }
    return first;
}

fn alternate_reads_local(choose_fresh: bool) -> i64[] {
    var values: i64[>..] = [30];
    if choose_fresh {
        return[values[0], 31];
    }
    values.push(32);
    return values;
}

fn same_local_twice() -> i64[], i64[] {
    var values: i64[>..] = [40];
    values.push(41);
    return values,
    values;
}

fn main() {
    print("named ", named_mutated());
    print("fresh ", independent_return(true), " calls ", fresh_calls);
    print("named alternate ", independent_return(false));
    print("different ", different_locals(true));
    print("reached ", alternate_reads_local(true), " ", alternate_reads_local(false));
    var first,
    second = same_local_twice();
    first[0] = 42;
    print("channels ", first, " ", second);
}
