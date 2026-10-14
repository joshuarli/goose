fn main() {
    let marker: u8[>..] = "x";
    let values: i64[>..] = [7, 11, 13];
    let flags: bool[>..] = [true, false, true];
    let empty: i64[>..] = [];
    let branch: i64[>..] = if values.len == 3 {
        [17, 19]
    } else {
        [23]
    };
    let grouped: i64[>..] = {
        [29, 31]
    };
    print(marker.len);
    print(values.len, " ", values[1]);
    print(flags.len, " ", flags[0], " ", flags[1], " ", flags[2]);
    print(empty.len);
    print(branch.len, " ", branch[1]);
    print(grouped.len, " ", grouped[0]);
}
