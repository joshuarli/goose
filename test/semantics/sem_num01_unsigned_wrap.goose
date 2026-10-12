// Unsigned addition, subtraction and multiplication wrap modulo 2^width at
// every width, in every build. Each result is computed at the operands' own
// width: a wrong implementation that computes in 64 bits and keeps the wide
// result prints 256 for the first line, or fails to wrap u64 at all.
fn add8(a: u8, b: u8) -> u8 {
    a + b
}

fn sub8(a: u8, b: u8) -> u8 {
    a - b
}

fn mul8(a: u8, b: u8) -> u8 {
    a * b
}

fn add16(a: u16, b: u16) -> u16 {
    a + b
}

fn sub16(a: u16, b: u16) -> u16 {
    a - b
}

fn mul16(a: u16, b: u16) -> u16 {
    a * b
}

fn add32(a: u32, b: u32) -> u32 {
    a + b
}

fn sub32(a: u32, b: u32) -> u32 {
    a - b
}

fn mul32(a: u32, b: u32) -> u32 {
    a * b
}

fn add64(a: u64, b: u64) -> u64 {
    a + b
}

fn sub64(a: u64, b: u64) -> u64 {
    a - b
}

fn mul64(a: u64, b: u64) -> u64 {
    a * b
}

fn main() {
    // Just inside the range: no wrap.
    print(add8(254, 1), " ", sub8(1, 1), " ", mul8(15, 17));
    // Just outside: wrap.
    print(add8(255, 1), " ", sub8(0, 1), " ", mul8(16, 16));
    print(add16(65535, 1), " ", sub16(0, 1), " ", mul16(256, 256));
    print(add32(4294967295, 1), " ", sub32(0, 1), " ", mul32(65536, 65536));
    print(add64(18446744073709551615, 1), " ", sub64(0, 1));
    print(mul64(4294967296, 4294967296), " ", mul64(18446744073709551615, 18446744073709551615));
    // A product that wraps to a nonzero value.
    print(mul8(200, 3), " ", mul32(65537, 65537));
}
