fn rebind(var view: i64[:], source: i64[:]) {
    view = source;
}

fn main() {
    let bytes: u8[>..] = "x";
    let values: i64[2] = [1, 2];
    rebind(values[..], values[..]);
    print(bytes.len);
}
