// `abort` ends the whole program from inside nested blocks and loops of a
// callee: nothing after it runs, in the callee or in any caller. The caller's
// line after the call is not printed, and neither is the second call. An
// implementation that treats abort like a `return` from the function prints
// "back in main" and a second search.
fn search(limit: i64) {
    for a in 0..limit {
        var b = 0;
        while b < limit {
            if a == 2 && b == 1 {
                print("giving up at ", a, " ", b);
                abort("search exhausted");
            }
            b += 1;
        }
        print("row ", a);
    }
}

fn main() {
    print("start");
    search(5);
    print("back in main");
    search(1);
}
