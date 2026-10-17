// runtime-debug
import std;

struct Tables { bytes: u8[>..]& }
struct View { bytes: const u8[:] }
struct Nested { view: View }

fn read(out: u8[>..]&) {
    out.clear();
    out.append("kept");
}

fn view(t: const Tables&) -> View {
    return View { bytes: t.bytes };
}

fn nested_view(t: const Tables&) -> Nested {
    return Nested { view: view(t) };
}

fn carried(t: Tables) -> View {
    return View { bytes: t.bytes };
}

fn deeper(tables: const Tables&) {
    let known = view(tables);
    let wrapped = nested_view(tables);
    let copied = carried(tables);
    var second: u8[>..] = [];
    read(second);
    print(known.bytes, " ", wrapped.view.bytes, " ", copied.bytes, " ", second);
}

fn apply<F>(tables: const Tables&) {
    F(view(tables));
}

fn main() {
    var first: u8[>..] = [];
    read(first);
    var tables = Tables { bytes: first };
    let known = view(tables);
    let wrapped = nested_view(tables);
    let copied = carried(tables);
    var second: u8[>..] = [];
    read(second);
    print(known.bytes, " ", wrapped.view.bytes, " ", copied.bytes, " ", second);
    deeper(tables);
    fn nested() {
        let captured = view(tables);
        var third: u8[>..] = [];
        read(third);
        print(captured.bytes, " ", third);
    }
    nested();
    apply(tables) { captured =>
        var fourth: u8[>..] = [];
        read(fourth);
        print(captured.bytes, " ", fourth);
    };
    for i in 2 {
        let repeated = view(tables);
        var later: u8[>..] = [];
        read(later);
        print(repeated.bytes, " ", later);
    }
}
