enum Value {
    Text { bytes: u8[varint] },
    Pair { left: i64, right: i64 },
}

fn main() {
    let values: Value..[] = [Value.Text { bytes: "goose" },
                             Value.Pair { left: 3, right: 5 }];
    for value in values {
        match value {
            Text &text => print(text.bytes),
            Pair &pair => print(pair.left + pair.right),
        }
    }
}
