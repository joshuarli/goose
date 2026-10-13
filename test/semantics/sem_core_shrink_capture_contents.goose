fn main() {
    let grow: i64[>..] = [1, 2];
    fn clear_grow() { grow.clear(); }
    clear_grow();

    let growshrink: i64[>..<] = [3, 4];
    fn write_growshrink() { growshrink[0] = 8; }
    write_growshrink();
    print(growshrink[0]);
    fn clear_growshrink() { growshrink.clear(); }
    clear_growshrink();

    let scalar: i64 = 7;
    fn show_scalar() { print(scalar); }
    show_scalar();
    print(grow.len, " ", growshrink.len);
}
