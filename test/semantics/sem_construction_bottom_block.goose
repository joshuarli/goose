// core-construction: fixture
fn leave() {
    return[4] from target;
}

fn target() -> i64[>..] {
    return[1, {
            leave();
            0
        }];
}

fn main() {
    var values = target();
    print(values[0]);
}
