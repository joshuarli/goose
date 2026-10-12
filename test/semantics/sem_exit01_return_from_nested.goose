// `return` from inside nested blocks and loops leaves them all and delivers
// its value, running nothing after it in the callee. Statements after the
// call in the caller still run, once. The search finds the first pair whose
// product is 12, with the inner loop restarted from its own bound for each
// outer value.
fn find_pair(target: i64) -> i64 {
    for a in 1..10 {
        var b = a;
        while b < 10 {
            if a * b == target {
                print("found ", a, " ", b);
                return a * 100 + b;
            }
            b += 1;
        }
        print("no pair starts at ", a);
    }
    return -1;
}

fn main() {
    print(find_pair(12));
    print(find_pair(97));
    print("done");
}
