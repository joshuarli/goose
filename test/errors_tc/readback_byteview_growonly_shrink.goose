// error: cannot clear cells while known is still used
struct Cell { v: i64 }
struct Tables { cells: Cell[>..]& }
struct View { bytes: const u8[:] }
fn view(t: const Tables&) -> View { return View { bytes: t.cells.bytes_of() }; }
fn main() {
    var cells: Cell[>..] = [Cell { v: 1 }];
    var tables = Tables { cells: cells };
    let known = view(tables);
    cells.clear();
    cells.push(Cell { v: 2 });
    print(known.bytes);
}
