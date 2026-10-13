struct Pair { left: i64, right: i64 }

fn main() {
    let original = Pair { left: 10, right: 20 };
    let copy = original;
    original.left = 99;
    print(original.left, " ", original.right, " ", copy.left, " ", copy.right);
}
