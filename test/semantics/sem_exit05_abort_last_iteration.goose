// The abort sits in the last iteration of the loop, after all the output of
// the earlier iterations and of the same iteration: every line before it is
// written, and nothing after the loop is. A guard that skips the abort on
// the final iteration, or an implementation that buffers output and drops it
// at an abort, prints something else.
fn main() {
    for i in 0..3 {
        print("iteration ", i);
        if i == 2 {
            print("aborting");
            abort("last iteration");
        }
    }
    print("not reached");
}
