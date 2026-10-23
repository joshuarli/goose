// error: storing a reference rooted at x, which does not outlive the destination (§9.2)
// f rebinds a field of the node h's holder points at, storage of the
// caller's that f cannot see, only bound by h; here it is n, which x does
// not outlive.
struct Node { p: i64? }
struct Holder { node: Node& }

fn f(h: Holder&, x: i64&) { h.node.p .= x; }

fn main() {
    var n = Node { p: null };
    {
        var x: i64 = 5;
        var h = Holder { node: n };
        f(h, x);
    }
    if n.p { print(n.p); }
}
