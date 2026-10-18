// error: storing a reference
struct Cell { v: i64 }
struct Tables { cells: Cell[>..<]& }
struct View { bytes: const u8[:] }
struct Nested { view: View }
fn bytes(t: const Tables&) -> const u8[:] { return t.cells.bytes_of(); }
fn view(t: const Tables&) -> Nested { return Nested { view: View { bytes: bytes(t) } }; }
fn main() {
    var cells: Cell[>..<] = [Cell { v: 1 }];
    var tables = Tables { cells: cells };
    let direct = bytes(tables);
    print(direct.len);
    let known = view(tables);
    cells.clear();
    cells.push(Cell { v: 2 });
    print(known.view.bytes);
}
