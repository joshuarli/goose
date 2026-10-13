fn set_value(value: i64&) { value = 9; }

fn main() {
    let values: i64[>..] = [1, 2];

    fn write_element() { values[0] = 3; }
    fn write_through_helper() { set_value(values[1]); }
    fn forward_write() { write_element(); }

    forward_write();
    write_through_helper();
    print(values[0], " ", values[1]);
}
