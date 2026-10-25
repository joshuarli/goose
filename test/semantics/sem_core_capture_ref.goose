fn bump(value: i64&) {
    value += 1;
}

fn through_parameter(reference: i64&) -> i64 {
    fn middle() -> i64 {
        fn inner() -> i64 {
            bump(reference);
            reference
        }
        inner()
    }
    middle()
}

fn read_parameter(reference: i64&) -> i64 {
    fn inner() -> i64 {
        reference
    }
    inner()
}

fn main() {
    var value: i64 = 10;
    let reference = &value;
    fn read() -> i64 {
        reference
    }
    fn borrow() -> i64& {
        reference
    }
    fn borrow_mixed() -> i64& {
        if value > 0 {
            reference
        } else {
            value
        }
    }
    fn middle() -> i64 {
        fn inner() -> i64 {
            let alias: i64& = reference;
            bump(alias);
            alias
        }
        inner()
    }
    print(read());
    value = 20;
    print(read());
    print(middle());
    bump(borrow());
    print(value);
    print(through_parameter(reference));
    bump(borrow_mixed());
    print(value);
    let fixed: i64 = 30;
    let readonly: const i64& = fixed;
    fn read_fixed() -> i64 {
        readonly
    }
    print(read_fixed());
    print(read_parameter(readonly));
    var count: i64 = 0;
    fn increment() {
        count += 1;
    }
    increment();
    print(count);
    var cells: i64[2] = [40, 50];
    let first = &cells[0];
    let second = &cells[1];
    fn choose(first_cell: bool) -> i64& {
        if first_cell {
            first
        } else {
            second
        }
    }
    bump(choose(true));
    bump(choose(false));
    print(cells[0], " ", cells[1]);
}
