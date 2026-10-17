// warning: `values` is copied on return rather than built where the result goes: another return's value may read or write it
// warning: `values` is copied on return rather than built where the result goes: another return's value may read or write it
// warning: `values` is copied on return rather than built where the result goes: another return's value may read or write it
// warning: `values` is copied on return rather than built where the result goes: another return's value may read or write it
fn mutate(values: i64[>..]&) {
    values.clear();
    values.push(6);
}

fn fresh() -> i64[>..] {
    return[7];
}

fn direct() -> i64[>..], i64[>..] {
    var values: i64[>..] = [1, 2];
    return values,
    {
        values.clear();
        values.push(3);
        [9]
    };
}

fn aliased() -> i64[>..], i64[>..] {
    var values: i64[>..] = [4, 5];
    var alias = values;
    return values,
    {
        mutate(alias);
        [10]
    };
}

fn captured() -> i64[>..], i64[>..] {
    var values: i64[>..] = [6, 7];
    fn clear_local() {
        values.clear();
        values.push(8);
    }
    return values,
    {
        clear_local();
        [11]
    };
}

fn branched(mutating: bool) -> i64[>..], i64[>..] {
    var values: i64[>..] = [12, 13];
    if mutating {
        return values,
        {
            values.clear();
            values.push(14);
            [15]
        };
    }
    return values,
    [16];
}

fn independent() -> i64[>..], i64[>..] {
    var values: i64[>..] = [17, 18];
    return values,
    fresh();
}

fn duplicate() -> i64[>..], i64[>..] {
    var values: i64[>..] = [14, 15];
    return values,
    values;
}

fn main() {
    let direct_first,
    direct_second = direct();
    print(direct_first, " ", direct_second);
    let alias_first,
    alias_second = aliased();
    print(alias_first, " ", alias_second);
    let captured_first,
    captured_second = captured();
    print(captured_first, " ", captured_second);
    let branch_first,
    branch_second = branched(true);
    print(branch_first, " ", branch_second);
    let no_mutation_first,
    no_mutation_second = branched(false);
    print(no_mutation_first, " ", no_mutation_second);
    let independent_first,
    independent_second = independent();
    print(independent_first, " ", independent_second);
    let duplicate_first,
    duplicate_second = duplicate();
    duplicate_first[0] = 99;
    print(duplicate_first, " ", duplicate_second);
}
