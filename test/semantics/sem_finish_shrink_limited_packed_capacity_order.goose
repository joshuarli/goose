// runtime-debug
struct Packed {
    tag: u8,
    value: i64
}

fn main() {
    var values: Packed[..1] = [Packed {
            tag: 1,
            value: 101
        }];
    fn size() -> i64 {
        print("size");
        return 2;
    }
    fn fill() -> Packed {
        print("fill");
        return Packed {
            tag: 2,
            value: 202
        };
    }
    values.resize(size(), fill());
}
