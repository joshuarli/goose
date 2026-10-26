// core-construction: fixture
fn consume(values: i64[]) {
    print(values.len);
}

fn main() {
    let limited: i64[..4] = [5, 6];
    fn clear_limited() {
        limited.clear();
    }
    print(limited.len);
    clear_limited();
    print(limited.len);
    let owned: i64[] = [7];
    consume(copy(owned));
}
