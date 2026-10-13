// core-pilot: legacy-only
// The two earlier appends finish before the third initializer exits from the
// append operation. The unfinished literal contributes no elements.

fn first() -> u8[] { print("first"); return "pending one"; }
fn second() -> u8[] { print("second"); return "pending two"; }
fn third() -> u8[] { print("third"); return "escaped" from append_values; }

fn append_values(out: u8[][>..]&) -> u8[] {
    print("begin");
    out.append(["one"]);
    out.append(["two"]);
    out.append([first(), second(), third()]);
    out.append(["not reached"]);
    return "normal";
}

fn main() {
    var out: u8[][>..] = ["start"];
    let result = append_values(out);
    print(out, " ", result);
}
