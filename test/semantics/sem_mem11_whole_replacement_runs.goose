// Whole replacement accepts a literal run, a branch of literal runs, and a
// block yielding a literal run. Each replacement is published in order.
fn main() {
    var values: i64[>..<] = [1, 2, 3];
    values = [4, 5];
    print(values.len, " ", values[0], " ", values[1]);

    values = if true { [6] } else { [7, 8] };
    print(values.len, " ", values[0]);

    let seed = 12;
    values = {
        let first = seed;
        [first, first + 1]
    };
    print(values.len, " ", values[0], " ", values[1]);
}
