struct Holder {
    r: i64&,
    s: const u8[:]
}

fn bump(r: i64&) {
    r = r + 1;
}

fn main() {
    var x = 5;
    const h: Holder = Holder {
        r: x,
        s: "local"
    };
    bump(h.r);
    print(x);
}
