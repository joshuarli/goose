fn main() {
    let bytes: u8[>..] = "A\0B";
    let selected: i64 = if bytes.len == 3 {
        1
    } else {
        2
    };
    let branch: u8[>..] = if bytes.len == 3 {
        "C\0D"
    } else {
        "E"
    };
    let data: u8[>..] = {
        "F\0G"
    };
    print(selected);
    print(bytes.len, " ", bytes[0], " ", bytes[2]);
    print(branch.len, " ", branch[2]);
    print(data.len, " ", data[1]);
}
