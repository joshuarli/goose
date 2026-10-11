fn add_guard(x: i8) -> bool {
    let sum = x + 1;
    if sum < x { return true; }
    false
}

fn subtract_guard(x: i8) -> bool {
    let difference = x - 1;
    if difference > x { return true; }
    false
}

fn wrong_add_relation(x: i8) -> bool {
    let sum = x + 1;
    if sum > x { return true; }
    false
}

fn wrong_add_operand(x: i8, y: i8) -> bool {
    let sum = x + 1;
    if sum < y { return true; }
    false
}

fn negative_increment(x: i8) -> bool {
    let sum = x + -1;
    if sum < x { return true; }
    false
}

fn unsigned_add(x: u8) -> bool {
    let sum = x + 1;
    if sum < x { return true; }
    false
}

fn stale_view() -> i32 {
    var values: i32[>..] = [1];
    let view = values[..];
    values.push(2);
    let last = view[values.len - 1];
    return last;
}

fn prefix_snapshot() -> i32 {
    var values: i32[>..] = [1];
    let view = values[..];
    values.push(2);
    let first = view[0];
    return first;
}

fn view_after_growth() -> i32 {
    var values: i32[>..] = [1];
    values.push(2);
    let view = values[..];
    let last = view[values.len - 1];
    return last;
}

fn unrelated_growth() -> i32 {
    var values: i32[>..] = [1];
    var other: i32[>..] = [];
    let view = values[..];
    other.push(2);
    let last = view[values.len - 1];
    return last;
}

fn main() {
    add_guard(1);
    subtract_guard(1);
    wrong_add_relation(1);
    wrong_add_operand(1, 2);
    negative_increment(1);
    unsigned_add(1);
    print(stale_view());
    print(prefix_snapshot(), view_after_growth(), unrelated_growth());
}
