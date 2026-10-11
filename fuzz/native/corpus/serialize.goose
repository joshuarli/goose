struct Node { tag: u8, next: Node&<u64>? }

fn main() {
    let image: u8[10] = [9, 9, 255, 255, 255, 255, 255, 255, 255, 127];
    let nodes, ok = from_bytes<Node[>..]>(image);
    print(ok, " ", nodes.len);
}
