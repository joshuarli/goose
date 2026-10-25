struct Packed {
    tag: u8,
    value: i64
}

fn pop_and_replace(values: Packed[>..<]&) {
    let removed = values.pop();
    print("pop ", removed.value);
    values = [Packed {
            tag: 4,
            value: 404
        }];
}

fn read_first(values: Packed[>..<]&) -> Packed {
    return values[0];
}

fn main() {
    let values: Packed[>..<] = [
        Packed {
            tag: 1,
            value: 101
        },
        Packed {
            tag: 2,
            value: 202
        },
    ];
    var sibling: Packed[>..<] = [Packed {
            tag: 7,
            value: 707
        }];
    let snapshot = read_first(sibling);
    print("snapshot ", snapshot.value);
    pop_and_replace(values);
    print(values.len, " ", values[0].value, " ", sibling[0].value);
}
