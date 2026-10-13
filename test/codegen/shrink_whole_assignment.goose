var branch_number = 0;

fn choose_first() -> bool {
    branch_number += 1;
    return branch_number % 2 == 1;
}

fn replacement_value() -> i64 {
    print("rhs");
    return 10;
}

fn main() {
    var values: i64[>..<] = [1];
    values = [2, 3];
    print(values);

    values = if choose_first() {
        [4]
    } else {
        [5, 6]
    };
    print(values);

    values = if choose_first() {
        [7]
    } else {
        [8, 9]
    };
    print(values);

    values = {
        let next = replacement_value();
        [next]
    };
    print(values);
}
