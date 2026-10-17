struct Packed {
    tag: u8,
    value: i64
}

fn clear_values(values: Packed[..2]&) {
    values.clear();
}

fn main() {
    var values: Packed[..2] = [
        Packed {
            tag: 1,
            value: 101
        },
        Packed {
            tag: 2,
            value: 202
        },
    ];
    let kept = &values[0].value;
    clear_values(values);
    print(values.len, " ", kept);
    values.push(Packed {
            tag: 3,
            value: 303
        });
    print(values.len, " ", kept, " ", values[0].value);
}
