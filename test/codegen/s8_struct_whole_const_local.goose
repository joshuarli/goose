struct Record {
    value: i64
}

fn main() {
    let frozen: const Record = Record {
        value: 3
    };
    print(frozen.value)
}
