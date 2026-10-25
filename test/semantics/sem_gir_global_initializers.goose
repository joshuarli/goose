struct Packed {
    tag: u8,
    value: i64
}

fn seed() -> i64 {
    return 41;
}

var count: i64 = seed();
var ready: bool = true;
var numbers: i64[2] = [7, 11];
var packed: Packed = Packed {
    tag: 3,
    value: 13
};

fn main() {
    print(count, " ", ready, " ", numbers[0], " ", numbers[1], " ", packed.tag, " ", packed.value, " ", seed());
}
