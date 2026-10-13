// error: the block's value is a slice rooted at a temporary, which does not outlive it
// Branches that are all [] take a slice parameter's element type,
// each a temporary array of its branch, as a literal with elements is
// (branch_join_literal_argument), which ends with the branch.
fn total(xs: const i64[:]) -> i64 { xs.len }
fn main() {
    let c = true;
    print(total(if c { [] } else { [] }));
}
