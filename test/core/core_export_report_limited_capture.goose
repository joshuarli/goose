fn main() {
    let limited: i64[..4] = [5, 6];
    fn clear_limited() { limited.clear(); }
    clear_limited();
}
