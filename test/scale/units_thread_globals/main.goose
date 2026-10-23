import small;
import wide;
thread_fn worker() {
    assert(next_small() == 2);
    assert(next_wide() == 101);
}
fn main() {
    assert(thread_wait(thread_spawn_contained(worker)));
    assert(next_small() == 2);
    assert(next_wide() == 101);
    print("isolated");
}
