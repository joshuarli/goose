// core-pilot: legacy-only
// An abort during an element run keeps earlier output and publishes no partial run.
fn first() -> i64[] {
    print("first");
    return[1];
}

fn fail() -> i64[] {
    print("failing");
    assert(false);
    return[2];
}

fn later() -> i64[] {
    print("later");
    return[3];
}

fn main() {
    var rows: i64[][>..] = [];
    rows.push([0]);
    print("before");
    rows.append([first(), fail(), later()]);
    print("unreachable");
}
