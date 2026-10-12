"""Source edits of the qualification matrix, as transformations of one
program.

`EditTargets(edit)` declares a group of functions for each kind of edit. With
`edit=None` it writes the original; with an edit identifier it writes the
program after that edit. Groups never share a function, so an edit touches
only its own group and the functions that call into it. Every function that
an edit is about is `recursive` (or called twice from a recursive caller)
so that it stays out of line at -O2 and its C can be compared.

Expectations are stated per edit in EDITS: the source functions whose
emitted code is expected to change, and the outcome.
"""

from dataclasses import dataclass, field

from model import FnExpect, Member


@dataclass(frozen=True)
class Edit:
    id: str
    title: str
    # Source functions whose emitted code (with source line numbers masked)
    # is expected to change. Not a count of implementations: a function that
    # gains a body also counts.
    changed: tuple = ()
    # "output": the edited program compiles and prints its expected output.
    # "error": it must fail to compile, with a diagnostic holding `message`.
    # "warning": it compiles and prints the original output, with a new
    # diagnostic holding `message`.
    outcome: str = "output"
    message: str = ""
    # Edits that run as a sequence rather than a single transformation.
    sequence: tuple = ()
    why: str = ""


EDITS = {e.id: e for e in (
    Edit("E02", "comment and blank line added above a function", (),
         why="only source line numbers move; no function's body changes"),
    Edit("E03", "body of a leaf that is not inlined", ("ed_leaf",),
         why="recursive, so no caller holds a copy"),
    Edit("E04", "body of a small helper that is inlined", ("ed_inl_a", "ed_inl_b"),
         why="the helper is pasted into its two callers and has no body of its own at -O2; "
             "the caller that does not call it is unchanged"),
    Edit("E05", "signature change with callers updated", ("ed_sig", "ed_sig_a", "ed_sig_b")),
    Edit("E06", "field added to a struct", ("ed_rec_user",),
         why="the function that builds the struct changes; one that never names it does not"),
    Edit("E07a", "a call passes a local where it passed a global", ("ed_ctx_caller", "main"),
         why="the callee reads only a length, so its body is the same under either root; the "
             "caller now owns a stack, so it takes a hidden stack argument and main's call "
             "to it changes"),
    Edit("E07b", "a call passes a pool where it passed a plain array",
         ("ed_pool_user", "ed_pool_callee"),
         why="the callee gains an instance for the pool form; the other caller keeps its plain one"),
    Edit("E07c", "a callee gains a shrink of its parameter", (), outcome="error",
         message="cannot call ed_shrink_callee, which shrinks arr",
         why="the caller holds a view of the array across the call"),
    Edit("E08", "a specialization request added", ("ed_spec_user", "ed_gen"),
         why="its removal is the original program"),
    Edit("E09a", "an overload added that wins at one call site", ("ed_over_u8",),
         why="the call with a u8 now resolves to the new overload; the i64 call does not"),
    Edit("E09b", "an import changed to a module providing the same name", ("ed_imp_value",)),
    Edit("E09c", "an embedded file's content changed", ("gs_init_globals",),
         why="the embedded bytes are static data and the global initializer is the only code "
             "that names them; the function reading the global is unchanged"),
    Edit("E15a", "an edit introducing a compile error", (), outcome="error",
         message="unknown function: ed_missing"),
    Edit("E15b", "an edit introducing a new warning", (), outcome="warning",
         message="redundant &"),
    Edit("E16", "an edit and its exact revert", ("ed_leaf",), sequence=("E03", "revert"),
         why="the edit is E03; the revert is the original program"),
)}

# Rows of the qualification matrix that are not source edits of one program.
NOT_SOURCE_EDITS = {
    "E00": "no edit: the original program",
    "E01": "a second build of an unchanged program; needs a build store",
    "E10": "changes the compiler, C compiler, flags or target, not the source",
    "E11": "deletes a build store",
    "E12": "corrupts a build store",
    "E13": "kills a build mid-publish",
    "E14": "runs two builds at once",
}

EMBED_BEFORE = "alpha\n"
EMBED_AFTER = "alpha beta\n"


def edit_for(edit_id):
    """The Edit whose transformation applies to the program, resolving a
    sequence to the edit it starts with."""
    e = EDITS[edit_id]
    return EDITS[e.sequence[0]] if e.sequence else e


class EditTargets(Member):
    kind = "edit_targets"
    name = "edit_targets"

    def __init__(self, edit=None):
        self.edit = edit_for(edit).id if edit else None

    def is_(self, *ids):
        return self.edit in ids

    def imports(self):
        return ["import ed_alt_b;" if self.is_("E09b") else "import ed_alt_a;"]

    def files(self):
        return {
            "ed_alt_a.goose": self.alt_module(1000),
            "ed_alt_b.goose": self.alt_module(2000),
            "ed_embed.txt": EMBED_AFTER if self.is_("E09c") else EMBED_BEFORE,
        }

    @staticmethod
    def alt_module(offset):
        return "\n".join([
            "recursive fn ed_imp_value(n: i64, k: i64) -> i64 {",
            f"    if k == 0 {{ return n + {offset}; }}",
            "    return ed_imp_value(n, k - 1);",
            "}", ""])

    def globals(self):
        e = self.is_
        out = []

        # Leaf, not inlined (E02 puts a comment and a blank line above it).
        if e("E02"):
            out += ["// Walks x up by n, then scales it.", ""]
        leaf_const = 2 if e("E03") else 1
        leaf_body = "ed_missing(x)" if e("E15a") else f"x * 3 + {leaf_const}"
        out += ["recursive fn ed_leaf(x: i64, n: i64) -> i64 {",
                f"    if n == 0 {{ return {leaf_body}; }}",
                "    return ed_leaf(x + 1, n - 1);",
                "}",
                "recursive fn ed_leaf_user(n: i64) -> i64 {",
                "    if n == 0 { return ed_leaf(5, 2); }",
                "    return ed_leaf_user(n - 1);",
                "}"]

        # A small helper inlined into two callers; a third never calls it.
        out += [f"fn ed_small(x: i64) -> i64 {{ return x + {2 if e('E04') else 1}; }}"]
        # Nothing is inlined into a recursive function, so the callers are
        # not recursive; they are long enough, and called twice, to stay
        # out of line themselves.
        for name, ret in (("a", "ed_small(10)"), ("b", "ed_small(20) * 2"), ("c", "5")):
            out += self.padded(f"ed_inl_{name}", ret)

        # A function whose signature changes with its callers.
        if e("E05"):
            out += ["recursive fn ed_sig(a: i64, b: i64, n: i64) -> i64 {",
                    "    if n == 0 { return a * 2 + b; }",
                    "    return ed_sig(a, b, n - 1);",
                    "}"]
            calls = {"a": "ed_sig(7, 100, 1)", "b": "ed_sig(9, 200, 1)"}
        else:
            out += ["recursive fn ed_sig(a: i64, n: i64) -> i64 {",
                    "    if n == 0 { return a * 2; }",
                    "    return ed_sig(a, n - 1);",
                    "}"]
            calls = {"a": "ed_sig(7, 1)", "b": "ed_sig(9, 1)"}
        for name in "ab":
            out += [f"recursive fn ed_sig_{name}(n: i64) -> i64 {{",
                    f"    if n == 0 {{ return {calls[name]}; }}",
                    f"    return ed_sig_{name}(n - 1);",
                    "}"]

        # A struct that gains a field; one function builds it, one does not.
        out += ["struct EdRec {", "    a: i64,", "    b: i64,"]
        if e("E06"):
            out += ["    c: i64 = 9,"]
        out += ["}",
                "recursive fn ed_rec_user(n: i64) -> i64 {",
                "    if n == 0 { let r = EdRec { a: 1, b: 2 }; return r.a + r.b; }",
                "    return ed_rec_user(n - 1);",
                "}",
                "recursive fn ed_rec_other(n: i64) -> i64 {",
                "    if n == 0 { return 4; }",
                "    return ed_rec_other(n - 1);",
                "}"]

        # A call that passes a global, or after E07a a local.
        out += ["var ed_g: i64[>..] = [1, 2, 3];",
                "recursive fn ed_ctx_callee(a: i64[:], n: i64) -> i64 {",
                "    if n == 0 { return a.len; }",
                "    return ed_ctx_callee(a, n - 1);",
                "}",
                "recursive fn ed_ctx_caller(n: i64) -> i64 {"]
        if e("E07a"):
            out += ["    if n == 0 { var l: i64[>..] = [4, 5]; return ed_ctx_callee(l, 1); }"]
        else:
            out += ["    if n == 0 { return ed_ctx_callee(ed_g, 1); }"]
        out += ["    return ed_ctx_caller(n - 1);", "}"]

        # A call that passes a plain array, or after E07b a pool.
        out += ["recursive fn ed_pool_callee(p: i64[>..]&, n: i64) -> i64 {",
                "    if n == 0 { p.push(1); return p.len; }",
                "    return ed_pool_callee(p, n - 1);",
                "}",
                "recursive fn ed_pool_plain(n: i64) -> i64 {",
                "    if n == 0 { var arr: i64[>..] = [1, 2, 3]; return ed_pool_callee(arr, 1); }",
                "    return ed_pool_plain(n - 1);",
                "}",
                "recursive fn ed_pool_user(n: i64) -> i64 {"]
        pool = "reusable var" if e("E07b") else "var"
        out += [f"    if n == 0 {{ {pool} arr: i64[>..] = [1, 2]; return ed_pool_callee(arr, 1); }}",
                "    return ed_pool_user(n - 1);",
                "}"]

        # A callee that gains a shrink while a caller holds a view.
        shrink = "a.pop(); " if e("E07c") else ""
        out += ["recursive fn ed_shrink_callee(a: i64[>..]&, n: i64) -> i64 {",
                f"    if n == 0 {{ {shrink}return a.len; }}",
                "    return ed_shrink_callee(a, n - 1);",
                "}",
                "recursive fn ed_shrink_caller(n: i64) -> i64 {",
                "    if n == 0 {",
                "        var arr: i64[>..] = [1, 2, 3];",
                "        let v = arr[..];",
                "        let k = ed_shrink_callee(arr, 1);",
                "        return k + v.len;",
                "    }",
                "    return ed_shrink_caller(n - 1);",
                "}"]

        # A generic function that gains an instantiation.
        out += ["recursive fn ed_gen<T>(x: T, n: i64) -> i64 {",
                "    if n == 0 { return x; }",
                "    return ed_gen(x, n - 1);",
                "}",
                "recursive fn ed_spec_user(n: i64) -> i64 {",
                "    if n == 0 {",
                "        var a: i64 = 40;"]
        if e("E08"):
            out += ["        var h: u16 = 2;", "        return ed_gen(a, 1) + ed_gen(h, 1);"]
        else:
            out += ["        return ed_gen(a, 1);"]
        out += ["    }", "    return ed_spec_user(n - 1);", "}"]

        # An overload that wins at one of two call sites.
        out += ["fn ed_over(x: i64) -> i64 { return x + 100; }"]
        if e("E09a"):
            out += ["fn ed_over(x: u8) -> i64 { return x + 200; }"]
        out += self.padded("ed_over_u8", "ed_over(b)", "var b: u8 = 5;")
        out += self.padded("ed_over_i64", "ed_over(c)", "var c: i64 = 6;")

        # A name provided by an imported module.
        out += ["recursive fn ed_imp_user(n: i64) -> i64 {",
                "    if n == 0 { return ed_imp_value(5, 1); }",
                "    return ed_imp_user(n - 1);",
                "}"]

        # An embedded file.
        out += ['let ED_TABLE: const u8[:] = embed_file("ed_embed.txt");',
                "recursive fn ed_embed_user(n: i64) -> i64 {",
                "    if n == 0 { return ED_TABLE.len; }",
                "    return ed_embed_user(n - 1);",
                "}"]

        # A call that is redundantly spelled by reference after E15b.
        out += ["fn ed_warn_inc(n: i64&) { n += 1; }",
                "recursive fn ed_warn_user(k: i64) -> i64 {"]
        amp = "&" if e("E15b") else ""
        out += [f"    if k == 0 {{ var a: i64 = 41; ed_warn_inc({amp}a); return a; }}",
                "    return ed_warn_user(k - 1);",
                "}"]
        return out

    @staticmethod
    def padded(name, result, setup=""):
        """A non-recursive function that returns `result` for 0 and stays
        out of line when called twice: its padding is arithmetic that leaves
        s at 0 for n = 0."""
        lines = [f"fn {name}(n: i64) -> i64 {{"]
        if setup:
            lines.append(f"    {setup}")
        lines.append("    var s: i64 = n;")
        lines += ["    s = s * 3 + n;" if i % 2 else "    if s > 1000 { s -= 7; }" for i in range(24)]
        return lines + [f"    if n == 0 {{ return {result} + s; }}", "    return s;", "}"]

    # Called with 0 once, or twice for the padded functions.
    CALLS = ("ed_leaf_user", "ed_inl_a", "ed_inl_b", "ed_inl_c", "ed_sig_a", "ed_sig_b",
             "ed_rec_user", "ed_rec_other", "ed_ctx_caller", "ed_pool_plain", "ed_pool_user",
             "ed_shrink_caller", "ed_spec_user", "ed_over_u8", "ed_over_i64", "ed_imp_user",
             "ed_embed_user", "ed_warn_user")
    TWICE = ("ed_inl_a", "ed_inl_b", "ed_inl_c", "ed_over_u8", "ed_over_i64")

    def calls(self):
        return [n for n in self.CALLS for _ in range(2 if n in self.TWICE else 1)]

    def body(self):
        return [f"print({name}(0));" for name in self.calls()]

    def output(self):
        e = self.is_
        values = {
            "ed_leaf_user": 23 if e("E03") else 22,
            "ed_inl_a": 12 if e("E04") else 11,
            "ed_inl_b": 44 if e("E04") else 42,
            "ed_inl_c": 5,
            "ed_sig_a": 114 if e("E05") else 14,
            "ed_sig_b": 218 if e("E05") else 18,
            "ed_rec_user": 3,
            "ed_rec_other": 4,
            "ed_ctx_caller": 2 if e("E07a") else 3,
            "ed_pool_plain": 4,
            "ed_pool_user": 3,
            "ed_shrink_caller": 6,
            "ed_spec_user": 42 if e("E08") else 40,
            "ed_over_u8": 205 if e("E09a") else 105,
            "ed_over_i64": 106,
            "ed_imp_user": 2005 if e("E09b") else 1005,
            "ed_embed_user": len(EMBED_AFTER if e("E09c") else EMBED_BEFORE),
            "ed_warn_user": 42,
        }
        return [str(values[name]) for name in self.calls()]

    def functions(self):
        e = self.is_
        fns = [FnExpect(n, 1, 1, 1) for n in (
            "ed_leaf", "ed_leaf_user", "ed_inl_a", "ed_inl_b", "ed_inl_c", "ed_sig", "ed_sig_a",
            "ed_sig_b", "ed_rec_user", "ed_rec_other", "ed_ctx_callee", "ed_ctx_caller",
            "ed_pool_plain", "ed_shrink_callee", "ed_shrink_caller", "ed_spec_user",
            "ed_over_u8", "ed_over_i64", "ed_imp_value", "ed_imp_user", "ed_embed_user",
            "ed_warn_user")]
        fns.append(FnExpect("ed_small", 1, 1, 1, inlined_at_o2=True))
        fns.append(FnExpect("ed_warn_inc", 1, 1, 1))
        fns.append(FnExpect("ed_pool_user", 1, 1, 1))
        fns.append(FnExpect("ed_pool_callee", 2 if e("E07b") else 1, 1,
                            2 if e("E07b") else 1))
        fns.append(FnExpect("ed_gen", 2 if e("E08") else 1, 2 if e("E08") else 1,
                            2 if e("E08") else 1))
        fns.append(FnExpect("ed_over", 2 if e("E09a") else 1, 2 if e("E09a") else 1,
                            2 if e("E09a") else 1, inlined_at_o2=True))
        return fns
