fn main() {
    var original: i64[>..<] = [1, 2, 3];
    var alternate: i64[>..<] = [8, 9];
    var current .= original;
    fn count() -> i64 {
        original.pop();
        current .= alternate;
        print("count");
        return 1;
    }
    current.pop_n(count());
    print(original, " ", alternate);

    var target: i64[>..<] = [10, 20, 30, 40];
    var another: i64[>..<] = [70];
    var receiver .= target;
    fn size() -> i64 {
        target.pop();
        receiver .= another;
        print("size");
        return 4;
    }
    fn fill() -> i64 {
        target.pop();
        print("fill");
        return 99;
    }
    receiver.resize(size(), fill());
    print(target, " ", another);
}
