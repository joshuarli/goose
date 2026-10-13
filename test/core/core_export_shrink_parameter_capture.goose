var global_values: i64[>..<] = [2];

fn main() {
    var local_values: i64[>..<] = [1];
    fn clear_local() {
        let reference .= global_values[0];
        local_values.clear();
        print(reference);
    }
    clear_local();
}
