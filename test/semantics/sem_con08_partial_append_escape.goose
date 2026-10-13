// Two variable-size elements finish one append before the third element's
// call returns from append_values. The caller keeps those elements and
// receives the nonlocal result; later appends do not run.
fn third() -> u8[][] { return ["escaped"] from append_values; }

fn append_values(out: u8[][>..]&) -> u8[][] {
    print("begin");
    out.append(["one", "two"]);
    out.append(third());
    out.append(["not reached"]);
    return ["normal"];
}

fn main() {
    var out: u8[][>..] = ["start"];
    let result = append_values(out);
    print(out, " ", result);
}
