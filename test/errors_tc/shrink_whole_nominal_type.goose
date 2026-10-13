// error: expected a value of type Left, got Right
struct Left {
    value: i64
}

struct Right {
    value: i64
}

fn main() {
    var values: Left[>..<] = [];
    values = [Right {
            value: 1
        }];
}
