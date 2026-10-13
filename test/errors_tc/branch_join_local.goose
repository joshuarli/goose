// error: the block's value is a slice rooted at t, which does not outlive it
// An array a branch gives where its construct's value is a slice is viewed
// where it lies, so it must outlive the construct: a local of the
// branch does not.
fn main() {
    let c = true;
    let s = if c { "none" } else { let t: u8[..8] = "abc"; t };
    print(s);
}
