fn append_and_return(values: i32[>..]&, value: i32) -> i32 {
    values.push(value);
    value
}

fn after_append(view: i32[:], value: i32) -> i64 {
    view.len
}

fn find_for(values: i32[>..]&, value: i32) -> i64 {
    for item, index in values {
        if item == value { return index; }
    }
    -1
}

fn use_index(values: i32[>..]&, index: i64) -> i32 {
    values[index]
}

fn main() {
    var first: i32[>..] = [1, 2];
    var second: i32[>..] = [1, 2];

    let stale_view = after_append(first[..], append_and_return(first, 3));
    let unrelated_view = after_append(first[..], append_and_return(second, 3));
    append_and_return(first, 4);
    let fresh_view = after_append(first[..], 0);
    let foreign_index = use_index(first, find_for(second, 2));
    let local_index = use_index(first, find_for(first, 2));
    let raw_index = use_index(first, 0);
    print(stale_view, unrelated_view, fresh_view, foreign_index, local_index, raw_index);
}
