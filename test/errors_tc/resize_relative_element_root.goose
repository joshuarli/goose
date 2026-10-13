// error: a relative reference must point within the same root as its location
// error: this reference is rooted at b
// resize stores its fill in every slot it adds, so a fill for
// relative-reference elements must point within the receiver's root, as a
// pushed element must.
struct Node { v: i64 }
struct Nest { nodes: Node[..4], links: (Node&<u16>?)[..4] }
fn main() {
    var a = Nest { nodes: [], links: [] };
    var b = Nest { nodes: [], links: [] };
    b.nodes.push(Node { v: 1 });
    a.links.resize(2, b.nodes[0]);
}
