// The reference programs the rejection fixtures for MEM-03 must not be
// confused with. A reference may be rebound to anything that outlives it: an
// outer variable stored in an inner block, a parameter returned to the
// caller, a global returned from a function, a slice of a parameter. An
// implementation that rejects (or miscompiles) these has made the root rule
// too strict.
var shared: i64 = 100;

fn pass(a: i64&) -> i64& {
    return a;
}

fn global_reference() -> i64& {
    return shared;
}

fn head(items: i64[:]) -> i64[:] {
    return items[0..2];
}

fn main() {
    var x = 1;
    var y = 2;
    var r .= x;
    {
        let alias .= y;
        r .= y;
        r .= x;
        alias = 20;
    }
    r .= pass(y);
    r += 5;
    print(x, " ", y, " ", r);

    var g .= global_reference();
    g += 1;
    print(shared);

    var items: i64[>..] = [7, 8, 9];
    let first_two = head(items);
    items[1] = 80;
    print(first_two.len, " ", first_two[1]);
}
