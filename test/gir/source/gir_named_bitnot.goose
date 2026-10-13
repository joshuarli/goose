// runtime-debug: a named `~` constant keeps the destination integer width in GIR.
let ROAD = 4;
let NOT_ROAD = ~ROAD;

struct Cell {
    flags: u8
}

fn main() {
    var c = Cell {
        flags: 7
    };
    c.flags &= NOT_ROAD;
    print(c.flags);
}
