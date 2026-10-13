// core-pilot: legacy-only
// Multi-name receives and forwarding preserve the order of separate result channels.
var effects: i64[>..] = [];

fn fixed_value() -> i64 {
    effects.push(1);
    return 7;
}

fn variable_value() -> u8[] {
    effects.push(2);
    return[65, 66];
}

fn bool_value() -> bool {
    effects.push(3);
    return true;
}

fn source() -> i64, u8[], bool {
    return fixed_value(),
    variable_value(),
    bool_value();
}

fn forward() -> i64, u8[], bool {
    return source();
}

fn appended() -> u8[] {
    return[67, 68];
}

fn main() {
    let number,
    bytes,
    okay = forward();
    print("results ", number, " ", bytes, " ", okay);
    print("effects ", effects);

    var combined: u8[>..] = [90];
    combined.append(appended());
    print("run ", combined);
}
