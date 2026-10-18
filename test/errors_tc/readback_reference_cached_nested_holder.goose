// error: storing a reference
struct Cell { v: i64 }
struct Tables { cells: Cell[>..<]& }
struct View { cell: const Cell& }
struct Nested { view: View }
fn first(t: const Tables&) -> const Cell& { return t.cells[0]; }
fn view(t: const Tables&) -> Nested { return Nested { view: View { cell: first(t) } }; }
fn main() {
    var cells: Cell[>..<] = [Cell { v: 1 }];
    var tables = Tables { cells: cells };
    let direct = first(tables);
    print(direct.v);
    let known = view(tables);
    cells.clear();
    cells.push(Cell { v: 2 });
    print(known.view.cell.v);
}
