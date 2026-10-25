fn bytes() -> u8[] {
    return[65, 66];
}

fn main() {
    let value = bytes();
    var appended: u8[>..] = [];
    appended.append(bytes());
    print(value, " ", appended);
}
