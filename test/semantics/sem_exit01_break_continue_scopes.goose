// `break` and `continue` leave the scopes nested inside their loop, and only
// those: the locals of an inner block are gone, the loop's own and the
// outer ones are not. The inner loop's `continue` skips the rest of its body
// for odd values; its `break` ends only the inner loop; the outer loop then
// resumes. Counters are updated before the jumps so that an implementation
// that mishandles them loops forever or miscounts.
fn main() {
    var total = 0;
    var inner_runs = 0;
    var i = 0;
    while i < 4 {
        var base = i * 10;
        i += 1;
        var j = 0;
        while true {
            var step = j;
            j += 1;
            inner_runs += 1;
            if step % 2 == 1 {
                continue;
            }
            if step > 4 {
                break;
            }
            total += base + step;
        }
    }
    print(total, " ", inner_runs, " ", i);
}
