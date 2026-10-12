// A reference to a whole array is rebound by the index expression with `.=`.
// The access indexes the array the reference designated when the index began
// (and its length 3), and the new designation applies only afterwards.
fn main() {
    var first: i64[3] = [10, 20, 30];
    var second: i64[3] = [40, 50, 60];
    var current .= first;
    fn switch_array() -> i64 {
        current .= second;
        return 1;
    }
    print(current[switch_array()]);
    print(current[1]);
}
