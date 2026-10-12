// runtime-debug
// Unsigned shifts mask their count the same way and shift in zeroes on the
// right: u8 200 >> 1 is 100 and 128 >> 8 is 128 (count 8 masks to 0). An
// implementation that sign-extends unsigned values prints 228 for 200 >> 1,
// and one that shifts by the full count prints 0 for the over-wide counts.
fn shl8(x: u8, n: u8) -> u8 {
    x << n
}

fn shr8(x: u8, n: u8) -> u8 {
    x >> n
}

fn shl32(x: u32, n: u32) -> u32 {
    x << n
}

fn shr32(x: u32, n: u32) -> u32 {
    x >> n
}

fn shl64(x: u64, n: u64) -> u64 {
    x << n
}

fn shr64(x: u64, n: u64) -> u64 {
    x >> n
}

fn main() {
    print(shl8(1, 7), " ", shl8(1, 8), " ", shl8(3, 9), " ", shl8(1, 255));
    print(shr8(200, 1), " ", shr8(128, 7), " ", shr8(128, 8), " ", shr8(128, 9), " ", shr8(128, 255));
    print(shl32(1, 31), " ", shl32(1, 32), " ", shl32(5, 33), " ", shl32(1, 4294967295));
    print(shr32(4294967295, 1), " ", shr32(4294967295, 31), " ", shr32(4294967295, 32), " ", shr32(4294967295, 33));
    print(shl64(1, 63), " ", shl64(1, 64), " ", shl64(1, 65), " ", shl64(1, 18446744073709551615));
    print(shr64(18446744073709551615, 1), " ", shr64(18446744073709551615, 63), " ", shr64(18446744073709551615, 64));
}
