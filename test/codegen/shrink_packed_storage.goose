struct Packed {
    flag: u8,
    value: i64
}

fn remove_last(values: Packed[>..<]&) {
    values.pop();
}

fn main() {
    var limited: Packed[..2] = [
        Packed {
            flag: 1,
            value: 0x102030405060708
        },
        Packed {
            flag: 2,
            value: 0x203040506070809
        },
    ];
    let kept = &limited[0].value;
    limited[0].value = 33;
    limited.clear();
    print(kept, " ", limited.len);
    limited.push(Packed {
            flag: 3,
            value: 44
        });
    print(kept, " ", limited[0].value, " ", limited.len);

    var resizable: Packed[>..<] = [
        Packed {
            flag: 4,
            value: 55
        },
        Packed {
            flag: 5,
            value: 66
        },
    ];
    var marker = 17;
    remove_last(resizable);
    print(resizable.len, " ", marker);
    resizable.push(Packed {
            flag: 6,
            value: 77
        });
    resizable = [Packed {
            flag: 7,
            value: 88
        }];
    print(resizable, " ", marker);
}
