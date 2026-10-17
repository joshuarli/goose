// core-construction: fixture
fn payload(first: u8, last: u8) -> u8[>..], i64 {
    var bytes: u8[>..] = [first, 0, 255, last];
    return bytes,
    19;
}

fn main() {
    let bytes,
    code = payload(65, 66);
    print(bytes);
    exit(code);
}
