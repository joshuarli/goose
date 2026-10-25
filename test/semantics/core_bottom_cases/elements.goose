struct Pair {
    number: i64,
    flag: bool,
}

fn first_bool() -> bool {
    print("element");
    return false;
}

fn leave_bool() {
    print("leave");
    return [true] from bool_target;
}

fn bool_target() -> bool[>..] {
    return [first_bool(), {
        leave_bool();
        false
    }];
}

fn leave_nested() {
    return [[4, 5]] from nested_target;
}

fn nested_target() -> i64[2][>..] {
    return [{
        leave_nested();
        [0, 0]
    }];
}

fn leave_fill() {
    return [6, 7] from fill_target;
}

fn fill_target() -> i64[2] {
    return [{
        leave_fill();
        0
    }; 2];
}

fn leave_pair() {
    return Pair { number: 8, flag: true } from pair_target;
}

fn pair_target() -> Pair {
    return Pair { number: {
        leave_pair();
        0
    }, flag: true };
}

fn leave_pair_array() {
    return [Pair { number: 9, flag: false }] from pair_array_target;
}

fn pair_array_target() -> Pair[>..] {
    return [{
        leave_pair_array();
        Pair { number: 0, flag: false }
    }];
}

fn leave_variable() {
    return [[10]] from variable_target;
}

fn variable_target() -> i64[][>..] {
    return [{
        leave_variable();
        [0]
    }];
}

fn leave_direct() {
    return [11] from direct_target;
}

fn direct_target() -> i64[>..] {
    return [leave_direct()];
}

fn leave_branch() {
    return [12] from branch_target;
}

fn branch_target(flag: bool) -> i64[>..] {
    return [if flag {
        leave_branch();
        0
    } else {
        leave_branch();
        0
    }];
}

fn main() {
    print("start");
    let bools = bool_target();
    print(bools[0]);
    let nested = nested_target();
    print(nested[0][1]);
    let filled = fill_target();
    print(filled[1]);
    let pair = pair_target();
    print(pair.number, " ", pair.flag);
    let pairs = pair_array_target();
    print(pairs[0].number);
    let variable = variable_target();
    print(variable.len);
    let direct = direct_target();
    print(direct[0]);
    let branched = branch_target(true);
    print(branched[0]);
}
