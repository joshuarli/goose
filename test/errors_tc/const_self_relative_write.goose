// error: cannot assign through this path
// A self-relative reference is no more writable than the path to it,
// since it points within the value or array holding it: writing
// through the link of a `const` value writes the value.
struct Ring { next: Ring&<u8>, v: i64 }
fn main() {
    const r = Ring { next: self, v: 1 };
    r.next.v = 7;
    print(r.v);
}
