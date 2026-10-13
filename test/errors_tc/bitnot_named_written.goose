// error: F is bound to a writable reference here
// `~F` adapting to u8 relies on F keeping its value.

let F = 4;
fn bump(x: i64&) { x = 400; }

fn main() {
    let a: u8 = ~F;
    print(a);
    bump(F);
}
