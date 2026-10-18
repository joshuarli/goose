// error: cannot clear cells while known is still used
struct Cell { v: i64 }
struct View { bytes: const u8[:] }
struct Tables { prior: const View& }
fn view(t: const Tables&) -> View { return View { bytes: t.prior.bytes }; }
fn main() {
    var cells: Cell[>..] = [Cell { v: 1 }];
    var prior = View { bytes: cells.bytes_of() };
    var tables = Tables { prior: prior };
    let known = view(tables);
    cells.clear();
    cells.push(Cell { v: 2 });
    print(known.bytes);
}
