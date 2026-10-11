var shared = 40;

fn read<T>(value: T&) -> i64 {
    value
}

fn main() {
    var local = 2;
    print(read(shared) + read(local));
}
