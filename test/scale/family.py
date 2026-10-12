"""Members that multiply specializations, and members that must stay apart.

Every function here is declared `recursive` (or given a body too large to
inline) so that it survives optimization at -O2: the optimizer inlines a
small function into its callers and the C then holds no body to compare.

The shareable members vary one dimension of the calling context at a time;
each was found by experiment to create a further specialization of one
source function whose printed body does not change, and to leave the
emitted C identical once the numbering of specializations is masked. The
distinct members are the cases whose emitted bodies must differ.
"""

import itertools

from model import FnExpect, Member


def restricted_growth(n):
    """Every way to group n parameters by the array they name, as a tuple
    that numbers the groups in order of first appearance."""
    def extend(prefix, top):
        if len(prefix) == n:
            yield tuple(prefix)
            return
        for g in range(top + 1):
            yield from extend(prefix + [g], max(top, g + 1))

    yield from extend([], 0)


def weak_orders(blocks):
    """Ranks 0..r-1, each used, for the given number of local arrays: which
    is declared in the outermost block, which deeper, which alongside."""
    for ranks in itertools.product(range(blocks), repeat=blocks):
        if sorted(set(ranks)) == list(range(len(set(ranks)))):
            yield ranks


def root_patterns(params):
    """Every distinct root pattern of `params` slice parameters: which
    parameters name one array, whether each array is a global or a local,
    and the relative depth of the locals. Each is a tuple (groups, labels,
    ranks) with a rank only for a local array."""
    for groups in restricted_growth(params):
        blocks = max(groups) + 1
        for labels in itertools.product("GL", repeat=blocks):
            locals_ = [b for b in range(blocks) if labels[b] == "L"]
            for ranks in weak_orders(len(locals_)):
                by_block = dict(zip(locals_, ranks))
                yield groups, labels, tuple(by_block.get(b) for b in range(blocks))


class RootPatterns(Member):
    """`copies` functions of `params` slice parameters, called once under
    every root pattern. The checker distinguishes which parameters name the
    same array, global from local per array, and the relative depth of the
    locals; it does not distinguish which global, or how far apart two
    depths are. Specializations per function therefore equal the number of
    patterns, and none of them reads an element, so no check is removed in
    one context and kept in another."""

    kind = "shareable"

    def __init__(self, params, copies):
        self.params, self.copies = params, copies
        self.patterns = list(root_patterns(params))
        self.name = f"root_patterns_{params}"

    def fn(self, k):
        return f"rp{self.params}_{k}"

    def global_name(self, b):
        return f"gp{self.params}_{b}"

    @staticmethod
    def length(label, b):
        return b + 1 if label == "G" else b + 2

    def globals(self):
        lines = []
        for k in range(self.copies):
            ps = ", ".join(f"p{i}: i64[:]" for i in range(self.params))
            total = " + ".join(f"{i + 1} * p{i}.len" for i in range(self.params))
            lines += [f"recursive fn {self.fn(k)}({ps}, n: i64) -> i64 {{",
                      f"    if n == 0 {{ return {total} + {k}; }}",
                      f"    return {self.fn(k)}({', '.join(f'p{i}' for i in range(self.params))}, n - 1);",
                      "}"]
        for b in range(self.params):
            lines.append(f"var {self.global_name(b)}: i64[>..] = [{', '.join(['1'] * (b + 1))}];")
        return lines

    def array(self, pi, labels, ranks, b):
        if labels[b] == "G":
            return self.global_name(b)
        return f"lp{self.params}_{pi}_{b}"

    def body(self):
        lines = []
        for pi, (groups, labels, ranks) in enumerate(self.patterns):
            depth = len({r for r in ranks if r is not None})
            for level in range(depth):
                lines.append("{")
                for b, r in enumerate(ranks):
                    if r == level:
                        n = self.length("L", b)
                        lines.append(f"var {self.array(pi, labels, ranks, b)}: i64[>..] = "
                                     f"[{', '.join(['2'] * n)}];")
            args = ", ".join(self.array(pi, labels, ranks, g) for g in groups)
            for k in range(self.copies):
                lines.append(f"print({self.fn(k)}({args}, 1));")
            lines += ["}"] * depth
        return lines

    def output(self):
        lines = []
        for groups, labels, ranks in self.patterns:
            for k in range(self.copies):
                lines.append(str(sum((i + 1) * self.length(labels[g], g)
                                     for i, g in enumerate(groups)) + k))
        return lines

    def functions(self):
        return [FnExpect(self.fn(k), len(self.patterns), 1, 1) for k in range(self.copies)]


class ConstRefs(Member):
    """A slice parameter given a writable array and a read-only one."""

    kind = "shareable"
    name = "const_refs"

    def __init__(self, copies):
        self.copies = copies

    def globals(self):
        return [line for k in range(self.copies) for line in (
            f"recursive fn cr_{k}(a: i64[:], n: i64) -> i64 {{",
            f"    if n == 0 {{ return a.len + {k}; }}",
            f"    return cr_{k}(a, n - 1);",
            "}")]

    def body(self):
        return (["{", "var cr_w: i64[>..] = [1, 2];", "let cr_c: const i64[>..] = [3, 4, 5];"]
                + [f"print(cr_{k}({a}, 1));" for k in range(self.copies) for a in ("cr_w", "cr_c")]
                + ["}"])

    def output(self):
        return [str(n + k) for k in range(self.copies) for n in (2, 3)]

    def functions(self):
        return [FnExpect(f"cr_{k}", 2, 1, 1) for k in range(self.copies)]


class LiteralParams(Member):
    """An untyped function whose parameters are given a literal or a
    variable: each parameter is a literal parameter or not, so four
    specializations, and the literal's value is not part of any of them.
    The body is long enough that a spec used twice stays out of line."""

    kind = "shareable"
    name = "literal_params"
    ROUNDS = 30

    def __init__(self, copies):
        self.copies = copies

    def fn(self, k):
        return f"lit_{k}"

    @classmethod
    def model(cls, a, b, k):
        s = a + k
        for i in range(cls.ROUNDS):
            if s > 1000 + i:
                s -= i
            s += a * i + b
        return s

    def globals(self):
        lines = []
        for k in range(self.copies):
            lines += [f"fn {self.fn(k)}(a, b) {{", f"    var s: i64 = a + {k};"]
            for i in range(self.ROUNDS):
                lines += [f"    if s > {1000 + i} {{ s -= {i}; }}", f"    s += a * {i} + b;"]
            lines += ["    return s;", "}"]
        return lines

    # (a, b) as written at the call: a number is a literal, "x" the variable.
    CALLS = [(1, 2), (3, 4), ("x", 2), ("x", 5), (1, "x"), (6, "x"), ("x", "x"), ("x", "x")]
    X = 7

    def body(self):
        lines = [f"{{", f"var lit_x: i64 = {self.X};"]
        for k in range(self.copies):
            for a, b in self.CALLS:
                args = ", ".join("lit_x" if v == "x" else str(v) for v in (a, b))
                lines.append(f"print({self.fn(k)}({args}));")
        return lines + ["}"]

    def output(self):
        val = lambda v: self.X if v == "x" else v
        return [str(self.model(val(a), val(b), k))
                for k in range(self.copies) for a, b in self.CALLS]

    def functions(self):
        return [FnExpect(self.fn(k), 4, 1, 1) for k in range(self.copies)]


class NestedFunctions(Member):
    """Nested functions whose specialization depends on the enclosing
    function's state: a captured slice given a global or a local root, a
    narrowed optional seen narrowed or not, a captured reference rebound
    between two calls. Each host is recursive so that it stays out of line,
    and so is each nested function."""

    kind = "shareable"
    name = "nested_functions"

    def __init__(self, copies):
        self.copies = copies

    def globals(self):
        lines = ["var nc_g: i64[>..] = [1, 2, 3];"]
        for k in range(self.copies):
            lines += [
                f"recursive fn nc_{k}(a: i64[:], n: i64) -> i64 {{",
                f"    recursive fn nc_inner_{k}(m: i64) -> i64 {{",
                f"        if m == 0 {{ return a.len; }}",
                f"        return nc_inner_{k}(m - 1);",
                "    }",
                f"    if n == 0 {{ return nc_inner_{k}(1) + {k}; }}",
                f"    return nc_{k}(a, n - 1);",
                "}",
                f"recursive fn no_{k}(v: i64&, n: i64) -> i64 {{",
                f"    if n > 0 {{ return no_{k}(v, n - 1); }}",
                "    var o: i64? = v;",
                f"    recursive fn no_show_{k}(m: i64) -> i64 {{",
                "        if m == 0 { if o { return o; } return 0; }",
                f"        return no_show_{k}(m - 1);",
                "    }",
                f"    var s: i64 = no_show_{k}(1);",
                f"    if o {{ s += no_show_{k}(1); }}",
                f"    return s + {k};",
                "}",
                f"recursive fn rb_{k}(n: i64) -> i64 {{",
                f"    if n > 0 {{ return rb_{k}(n - 1); }}",
                "    var a: i64[>..] = [1];",
                "    var b: i64[>..] = [1, 2];",
                "    var r: i64[>..]& .= a;",
                f"    recursive fn rb_read_{k}(m: i64) -> i64 {{",
                "        if m == 0 { return r.len; }",
                f"        return rb_read_{k}(m - 1);",
                "    }",
                f"    let first = rb_read_{k}(1);",
                "    r .= b;",
                f"    return first * 10 + rb_read_{k}(1) + {k};",
                "}",
            ]
        return lines

    def body(self):
        lines = ["{", "var nc_l: i64[>..] = [1, 2];", "var no_v: i64 = 5;"]
        for k in range(self.copies):
            lines += [f"print(nc_{k}(nc_g, 1));", f"print(nc_{k}(nc_l, 1));",
                      f"print(no_{k}(no_v, 1));", f"print(rb_{k}(1));"]
        return lines + ["}"]

    def output(self):
        return [str(v) for k in range(self.copies) for v in (3 + k, 2 + k, 10 + k, 12 + k)]

    def functions(self):
        fns = []
        for k in range(self.copies):
            fns += [FnExpect(f"nc_{k}", 2, 1, 1), FnExpect(f"nc_inner_{k}", 2, 1, 1),
                    FnExpect(f"no_{k}", 1, 1, 1), FnExpect(f"no_show_{k}", 2, 1, 1),
                    FnExpect(f"rb_{k}", 1, 1, 1), FnExpect(f"rb_read_{k}", 2, 1, 1)]
        return fns


class Distinct(Member):
    """One instance of each case that must stay separate implementations,
    and one mutually recursive pair under two root contexts that shares as
    a pair. The rows of the table: different concrete argument types, a
    `reusable` pool against a plain resizable reference, different bound
    function values, a result consumed as a value against an element run,
    different nonlocal-return targets, a mutually recursive pair, and two
    reference parameters that name two arrays in one call and one array in
    another."""

    kind = "distinct"
    name = "distinct"
    APPLY_ROUNDS = 12

    @classmethod
    def apply(cls, factor, x):
        s = x
        for i in range(cls.APPLY_ROUNDS):
            s += factor * s + i
            if s > 900 + i:
                s -= i
        return s

    def globals(self):
        lines = [
            # Different concrete argument types.
            "recursive fn ds_types<T>(xs: T[:], n: i64) -> i64 {",
            "    if n == 0 { return xs[0]; }",
            "    return ds_types(xs, n - 1);",
            "}",
            # A pool against a plain resizable reference.
            "reusable var ds_pool: i64[>..] = [];",
            "recursive fn ds_pool_user(p: i64[>..]&, n: i64) -> i64 {",
            "    if n == 0 { p.push(1); return p.len; }",
            "    return ds_pool_user(p, n - 1);",
            "}",
            # Different bound function values.
            "fn ds_dbl(x: i64) -> i64 { return x * 2; }",
            "fn ds_tpl(x: i64) -> i64 { return x * 3; }",
            "fn ds_apply<F>(x: i64) -> i64 {",
            "    var s: i64 = x;",
        ]
        for i in range(self.APPLY_ROUNDS):
            lines += [f"    s += F(s) + {i};", f"    if s > {900 + i} {{ s -= {i}; }}"]
        lines += [
            "    return s;",
            "}",
            # A value against an element run.
            "recursive fn ds_mk(n: i64) -> i64[] {",
            "    if n == 0 { return [1, 2, 3]; }",
            "    return ds_mk(n - 1);",
            "}",
            # Nonlocal return propagated through ds_relay to either target.
            "fn ds_finish() { return 7 from ds_choose; }",
            "recursive fn ds_relay(n: i64) {",
            "    if n > 0 { ds_relay(n - 1); } else { ds_finish(); }",
            "}",
            "fn ds_choose<T>(x: T) -> T { ds_relay(2); return x; }",
            # A mutually recursive pair under a global and a local root.
            "var ds_pair_g: i64[>..] = [1];",
            "recursive fn ds_ping(a: i64[:], n: i64) -> i64 {",
            "    if n == 0 { return a.len; }",
            "    return ds_pong(a, n - 1);",
            "}",
            "recursive fn ds_pong(a: i64[:], n: i64) -> i64 {",
            "    if n == 0 { return a.len + 1; }",
            "    return ds_ping(a, n - 1);",
            "}",
            # Two parameters on two arrays, then on one: the body reads the
            # first's length, shrinks through the second, then indexes the
            # first. Both calls are accepted; the second reads the array it
            # shrank, so it must keep a check the first does not need.
            "recursive fn ds_two(a: i64[>..<]&, b: i64[>..<]&, n: i64) -> i64 {",
            "    if n == 0 {",
            "        let k = a.len;",
            "        b.pop();",
            "        return a[k - 2];",
            "    }",
            "    return ds_two(a, b, n - 1);",
            "}",
        ]
        return lines

    def body(self):
        return [
            "{",
            "var ds_i: i64[>..] = [11];",
            "var ds_j: i32[>..] = [22];",
            "print(ds_types(ds_i, 1));",
            "print(ds_types(ds_j, 1));",
            "var ds_plain: i64[>..] = [1];",
            "print(ds_pool_user(ds_plain, 1));",
            "print(ds_pool_user(ds_pool, 1));",
            "print(ds_apply(1, ds_dbl));",
            "print(ds_apply(1, ds_dbl));",
            "print(ds_apply(1, ds_tpl));",
            "print(ds_apply(1, ds_tpl));",
            "var ds_run: i64[>..] = [];",
            "ds_run.append(ds_mk(1));",
            "print(ds_run.len);",
            "var ds_rows: i64[][>..] = [];",
            "ds_rows.push(ds_mk(1));",
            "print(ds_rows.len);",
            "var ds_w: i64 = 1;",
            "var ds_s: u8 = 2;",
            "print(ds_choose(ds_w));",
            "print(ds_choose(ds_s));",
            "var ds_pair_l: i64[>..] = [2, 3];",
            "print(ds_ping(ds_pair_g, 3));",
            "print(ds_ping(ds_pair_l, 3));",
            "var ds_x: i64[>..<] = [1, 2, 3];",
            "var ds_y: i64[>..<] = [4, 5, 6];",
            "print(ds_two(ds_x, ds_y, 1));",
            "print(ds_two(ds_x, ds_x, 1));",
            "}",
        ]

    def output(self):
        return [str(v) for v in (
            11, 22, 2, 1,
            self.apply(2, 1), self.apply(2, 1), self.apply(3, 1), self.apply(3, 1),
            3, 1, 7, 7, 2, 3, 2, 2)]

    def functions(self):
        return [
            FnExpect("ds_types", 2, 2, 2),
            FnExpect("ds_pool_user", 2, 1, 2),
            FnExpect("ds_dbl", 1, 1, 1, inlined_at_o2=True),
            FnExpect("ds_tpl", 1, 1, 1, inlined_at_o2=True),
            FnExpect("ds_apply", 2, 1, 2),
            FnExpect("ds_mk", 1, 1, 2, note="one specialization, emitted once as a value "
                     "and once as an element run"),
            FnExpect("ds_finish", 2, 1, 2),
            FnExpect("ds_relay", 2, 1, 2),
            FnExpect("ds_choose", 2, 2, 2),
            FnExpect("ds_ping", 2, 1, 1),
            FnExpect("ds_pong", 2, 1, 1),
            FnExpect("ds_two", 2, 1, 2),
        ]

    def pairs(self):
        return [
            {"functions": ["ds_types"], "outcome": "distinct",
             "reason": "different element types give different layouts and operations"},
            {"functions": ["ds_pool_user"], "outcome": "distinct",
             "reason": "a pool reference carries its freelist, which changes the signature"},
            {"functions": ["ds_apply"], "outcome": "distinct",
             "reason": "different bound function values are different callees"},
            {"functions": ["ds_mk"], "outcome": "distinct",
             "reason": "a result requested as a value writes a header; as an element run it does not"},
            {"functions": ["ds_relay", "ds_finish"], "outcome": "distinct",
             "reason": "propagating a return to a different target tests a different discriminant"},
            {"functions": ["ds_two"], "outcome": "distinct",
             "reason": "two arrays let the body cache the second's stack top; one array cannot"},
            {"functions": ["ds_ping", "ds_pong"], "outcome": "share_as_pair",
             "reason": "the components are equal under a global and a local root"},
        ]
