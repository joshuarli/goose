struct Packed { tag: u8, value: i64, const stamp: i16 }

fn main() {
    let p = Packed { tag: 1, value: 40, stamp: 7 };
    p.value += 2;
    print(p.tag, " ", p.value, " ", p.stamp);
}
