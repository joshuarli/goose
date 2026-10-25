fn length(values: i64[>..]) -> i64 {
    return values.len;
}

fn main() {
    var dynamic: i64[>..] = [1];
    let items: i64[2] = [2, 3];
    let filled: i64[2] = [4; 2];
    let selected: i64 = if true {
        items[0]
    } else {
        0
    };
    let blocked: i64 = {
        let local = 6;
        local + selected
    };
    print(length(copy(dynamic)), " ", filled[1], " ", blocked);
    dynamic.push(blocked);
    print(dynamic[1]);
}
