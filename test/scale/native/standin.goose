// A program with C of its own that depends on the single-file form: the header
// reads the runtime's internals and spells `sl_Point_g`, a slice of Point, by
// the name single-file output gives it. Build it with
//   goose --standalone --include standin.h -o standin.c standin.goose
// or in units, `goose build --units --include standin.h standin.goose`.
struct Point { x: i64, y: i64 }

extern fn standin_runtime_messages() -> i64;
extern fn standin_sum(points: Point[:]) -> i64;
extern fn standin_scale(p: Point&, k: i64);

fn total(points: Point[:]) -> i64 {
    return standin_sum(points);
}

fn main() {
    var points: Point[>..] = [Point { x: 1, y: 2 }, Point { x: 3, y: 4 }];
    print(total(points));
    var p = Point { x: 5, y: 6 };
    standin_scale(p, 3);
    print(p.x + p.y);
    print(standin_runtime_messages());
}
