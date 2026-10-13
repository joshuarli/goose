struct Record {
    value: i64
}

fn make_record() -> Record {
    Record {
        value: 42
    }
}

fn main() {
    print(make_record().value)
}
