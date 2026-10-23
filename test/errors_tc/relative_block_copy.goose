// error: copying a value of type Node, which contains self-relative references, is not supported
struct Node { id: i64, me: Node&<u32> }
fn give<F>() { F() }
fn main() {
    let n = Node { id: 1, me: self };
    let x = give() { n };
    print(x.id);
}
