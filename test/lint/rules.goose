import std;

fn identity<T>(value: T) -> T {
    value
}

fn once<T>(value: T) -> T {
    value
}

fn ready() -> bool {
    true
}

fn maybe_trap(divisor: i64) {
    1 / divisor;
}

fn main() {
    let parsed, parsed_ok = parse_int("42");
    let parsed_value = parse_int("43");
    var overwritten, overwritten_ok = parse_int("45");
    overwritten_ok = false;
    if overwritten_ok { print(overwritten); }
    let checked, accepted = parse_int("44");
    if accepted {
        print(checked);
    }

    qpoll<i64>();
    let queued, received = qpoll<i64>();
    let scalar_poll = qpoll<i64>();
    let checked_poll, got_poll = qpoll<i64>();
    print(queued);
    print(got_poll, checked_poll);
    ready();
    maybe_trap(2);

    42;
    1 + 2;
    3.14;
    true;
    "unused string literal";

    let number = identity(1);
    let text = identity("one");
    once(2);
    print(number, text);
    print("target-program-ran");
}
