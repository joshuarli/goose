// error: break with a value exits loop/block only
// break with a value exits loop/block only.
fn main() {
    var i = 0;
    while i < 10 {
        i++;
        break 5;
    }
}
