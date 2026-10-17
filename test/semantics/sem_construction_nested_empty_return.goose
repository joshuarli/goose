fn leave(stop: bool) {
    if stop {
        return[67] from target;
    }
}

fn target(stop: bool) -> i64[>..] {
    return {
        leave(stop);
        [66]
    };
}

fn main() {
    var values = target(true);
    print(values[0]);
}
