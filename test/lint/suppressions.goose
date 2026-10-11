import std;

fn main() {
    let parsed, valid = parse_int("42"); // goose-lint: allow[discarded_failure] -- this fixture verifies local binding

    // goose-lint: allow[discarded_failure] -- first directive for this statement
    let duplicate_value, duplicate_status = parse_int("43"); // goose-lint: allow[discarded_failure] -- duplicate directive

    // goose-lint: allow[not_a_rule] -- typo is reported
    print("this string is not a directive");

    // goose-lint: allow[discarded_failure] -- no matching failure on the next statement
    let used = 2;
    print(used);

    // goose-lint: allow[discarded_failure]
    print("missing reason is malformed");

    let text = "goose-lint: allow[not_a_rule] -- this is ordinary string data";
}
