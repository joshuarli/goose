var word: u8[>..] = [119, 111, 114, 100];
var letters: u8[:] = word[..];
var count: i64 = 5;

fn get_letters() -> u8[:]& {
    letters
}

fn get_count() -> i64& {
    count
}

var copied_letters: u8[:] = get_letters();
var copied_count: i64 = get_count();

fn main() {
    print(copied_letters, " ", copied_count);
}
