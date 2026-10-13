struct Record {
    value: i64
}

fn read_value(record: const Record) -> i64 {
    record.value
}

fn main() {
    let record = Record {
        value: 5
    };
    print(read_value(record))
}
