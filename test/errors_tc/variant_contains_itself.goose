// error: variant L.Cons contains itself by value
// A variant type is its payload, so holding one by value in that
// payload makes it part of itself.
enum L { Nil, Cons { v: i64, next: L.Cons } }
fn main() {
    let l = L.Nil;
    print(l);
}
