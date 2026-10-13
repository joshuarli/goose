// error: in nums: i64[>..] cannot hold a value of type ENode, so nothing in it can be pointed at
// The pool must be storage the pointee can live in: nothing in an array of
// i64 is an ENode (the candidate notion of ).
struct ENode { key: i32, next: ENode&<u32 in nums>? }
var nums: i64[>..] = [];
var epool: ENode[>..] = [];
fn main() {
    nums.push(1);
    epool.push(ENode { key: 1 });
    print(epool.len);
}
