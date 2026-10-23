// error: a relative reference must point within the same root as its location
struct Node { id: i64, next: Node&<u32>? }
fn make(first: Node&) -> Node { Node { id: 2, next: first } }
fn main() {
    var a: Node[>..] = [Node { id: 1 }];
    a.push(block { make(a[0]); make(a[0]) });
}
