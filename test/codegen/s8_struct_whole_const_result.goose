struct Record {
    value: i64
}

fn make_record() -> const Record {
    Record {
        value: 7
    }
}

fn main() {
    let record: Record = make_record();
    print(record.value)
}
