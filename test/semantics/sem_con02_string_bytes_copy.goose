// core-pilot: legacy-only
// String literals are byte slices; constructed values and explicit copies keep raw bytes.
fn main() {
    let static: const u8[:] = "\0\xffA";
    let literal: u8[] = [0, 255, 'A'];
    var owned: u8[>..] = copy(literal);
    owned[0] = 1;

    print("static ", static.len, " ", static[0], " ", static[1], " ", static[2]);
    print("literal ", literal.len, " ", literal[0], " ", literal[1], " ", literal[2]);
    print("copy ", owned.len, " ", owned[0], " ", owned[1], " ", owned[2]);

    let text: u8[>..] = str("n=", 7);
    print("constructed ", text.len, " ", text[0], " ", text[1], " ", text[2]);
}
