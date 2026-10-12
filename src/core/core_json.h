// Goose compiler — Typed Goose Core, serialization.
//
// The wire format is JSON in which every record is an array whose first
// element is a tag string, with a fixed arity per tag; there are no objects.
// Tables are numbered by first mention in the document, so the same module
// always gives the same bytes: the writer emits the globals and the
// implementations first, interning types and origins as it meets them, and
// then prepends the tables those mentions built.
#pragma once

namespace goose {

inline constexpr const char *CORE_SCHEMA = "goose-core/0.2";
inline constexpr const char *CORE_PROFILE = "core-pilot";

// Whether the text is well-formed UTF-8 (no overlong forms, surrogates or
// values above U+10FFFF): the wire format carries text verbatim.
inline bool CoreIsUtf8(string_view s) {
    size_t i = 0;
    while (i < s.size()) {
        auto c = (uint8_t)s[i];
        size_t n;
        uint32_t cp;
        if (c < 0x80) { i++; continue; }
        else if (c >= 0xC2 && c <= 0xDF) { n = 1; cp = c & 0x1F; }
        else if (c >= 0xE0 && c <= 0xEF) { n = 2; cp = c & 0x0F; }
        else if (c >= 0xF0 && c <= 0xF4) { n = 3; cp = c & 0x07; }
        else return false;
        if (i + n >= s.size()) return false;
        for (size_t k = 1; k <= n; k++) {
            auto cc = (uint8_t)s[i + k];
            if ((cc & 0xC0) != 0x80) return false;
            cp = (cp << 6) | (cc & 0x3F);
        }
        if ((n == 2 && cp < 0x800) || (n == 3 && cp < 0x10000) || cp > 0x10FFFF ||
            (cp >= 0xD800 && cp <= 0xDFFF))
            return false;
        i += n + 1;
    }
    return true;
}

class CoreWriter {
public:
    explicit CoreWriter(const CoreModule &mod) : m(mod) {}

    string Write() {
        // The globals and implementations first: they are what mentions types
        // and origins.
        string objs = "[";
        for (size_t i = 0; i < m.globals.size(); i++) {
            if (i) objs += ',';
            Global(objs, m.globals[i]);
        }
        objs += "],[";
        for (size_t i = 0; i < m.impls.size(); i++) {
            if (i) objs += ',';
            Impl(objs, m.impls[i]);
        }
        objs += "],[";
        for (size_t i = 0; i < m.contexts.size(); i++) {
            if (i) objs += ',';
            Context(objs, m.contexts[i]);
        }
        objs += "]";
        // Files are numbered by first use in the origin table.
        filemap.assign(m.files.size(), -1);
        fileorder.clear();
        for (auto &o : origins) {
            if (filemap[o.file] < 0) {
                filemap[o.file] = (int)fileorder.size();
                fileorder.push_back(o.file);
            }
        }
        string out = cat("[\"module\",\"", CORE_SCHEMA, "\",\"", CORE_PROFILE, "\",[");
        for (size_t i = 0; i < fileorder.size(); i++) {
            if (i) out += ',';
            out += "[\"file\",";
            Str(out, m.files[fileorder[i]]);
            out += ']';
        }
        out += "],[";
        for (size_t i = 0; i < typeorder.size(); i++) {
            if (i) out += ',';
            TypeRecord(out, m.types[typeorder[i]]);
        }
        out += "],";
        out += objs;
        Append(out, ",", m.entry, ",[");
        for (size_t i = 0; i < origins.size(); i++) {
            if (i) out += ',';
            Append(out, "[\"origin\",", filemap[origins[i].file], ",", origins[i].line, ",\"",
                   CoreOriginKindName(origins[i].kind), "\"]");
        }
        out += "]]\n";
        return out;
    }

    // The numbering of files and origins the last Write() gave, which a
    // module lowered from this one keeps.
    vector<string> FileTable() const {
        vector<string> out;
        for (auto f : fileorder) out.push_back(m.files[f]);
        return out;
    }
    // Each origin with its file as numbered in the output.
    vector<CoreOrigin> OriginTable() const {
        auto out = origins;
        for (auto &o : out) o.file = filemap[o.file];
        return out;
    }
    // The number of an origin of this module.
    int OriginId(const CoreOrigin &o) const {
        return originnum.at(make_tuple(o.file, o.line, (int)o.kind));
    }

private:
    const CoreModule &m;
    vector<int> filemap, fileorder;
    unordered_map<CoreTypeId, int> typenum;
    vector<CoreTypeId> typeorder;
    vector<CoreOrigin> origins;
    // The origin table is small next to the tree, but a linear probe per
    // mention would still be quadratic; key by the triple.
    map<tuple<int, int, int>, int> originnum;

    int T(CoreTypeId id) {
        if (auto it = typenum.find(id); it != typenum.end()) return it->second;
        auto &t = m.types[id];
        if (t.elem >= 0) T(t.elem);
        auto n = (int)typeorder.size();
        typenum[id] = n;
        typeorder.push_back(id);
        return n;
    }

    int O(const CoreOrigin &o) {
        auto key = make_tuple(o.file, o.line, (int)o.kind);
        if (auto it = originnum.find(key); it != originnum.end()) return it->second;
        auto n = (int)origins.size();
        originnum[key] = n;
        origins.push_back(o);
        return n;
    }

    // The writer escapes only the quote, the backslash and the control
    // characters; every other byte is written as it is.
    static void Str(string &out, string_view s) {
        out += '"';
        for (auto c : s) {
            auto b = (unsigned char)c;
            if (c == '"') out += "\\\"";
            else if (c == '\\') out += "\\\\";
            else if (b < 0x20) {
                char hex[7];
                snprintf(hex, sizeof hex, "\\u%04x", b);
                out += hex;
            } else out += c;
        }
        out += '"';
    }

    void TypeRecord(string &out, const CoreType &t) {
        switch (t.kind) {
            case CoreType::Int: Append(out, "[\"int\",\"", CoreIntName(t.ity), "\"]"); break;
            case CoreType::Bool: out += "[\"bool\"]"; break;
            case CoreType::Unit: out += "[\"unit\"]"; break;
            case CoreType::Arr: Append(out, "[\"arr\",", typenum.at(t.elem), ",", t.count, "]"); break;
            case CoreType::Grow: Append(out, "[\"grow\",", typenum.at(t.elem), "]"); break;
            case CoreType::Ref:
                Append(out, "[\"ref\",\"", CoreMutName(t.mut), "\",", typenum.at(t.elem), "]");
                break;
            case CoreType::Slice:
                Append(out, "[\"slice\",\"", CoreMutName(t.mut), "\",", typenum.at(t.elem), "]");
                break;
            case CoreType::View:
                Append(out, "[\"view\",\"", CoreMutName(t.mut), "\",", typenum.at(t.elem), "]");
                break;
        }
    }

    void Global(string &out, const CoreGlobal &g) {
        out += "[\"global\",";
        Str(out, g.name);
        Append(out, ",", T(g.type), ",\"", g.kind == CoreVarKind::Var ? "var" : "let", "\",");
        Expr(out, *g.init);
        Append(out, ",", O(g.org), "]");
    }

    void Impl(string &out, const CoreImpl &im) {
        out += "[\"impl\",";
        Str(out, im.name);
        out += ",[";
        for (size_t i = 0; i < im.params.size(); i++) {
            if (i) out += ',';
            Append(out, "[\"param\",", im.params[i].var, ",\"",
                   im.params[i].byRef ? "by_ref" : "by_value", "\"]");
        }
        out += "],[";
        for (size_t i = 0; i < im.results.size(); i++) {
            if (i) out += ',';
            Append(out, T(im.results[i]));
        }
        out += "],[";
        for (size_t i = 0; i < im.vars.size(); i++) {
            if (i) out += ',';
            auto &v = im.vars[i];
            out += "[\"local\",";
            Str(out, v.name);
            Append(out, ",", T(v.type), ",\"", v.kind == CoreVarKind::Var ? "var" : "let", "\",",
                   v.scope, ",", O(v.org), "]");
        }
        out += "],";
        Block(out, im.body);
        out += ",";
        Summary(out, im.summary);
        out += "]";
    }

    static void Targets(string &out, const vector<CoreTarget> &ts) {
        out += '[';
        for (size_t i = 0; i < ts.size(); i++) {
            if (i) out += ',';
            Append(out, ts[i].global ? "[\"t_global\"," : "[\"t_param\",", ts[i].index, "]");
        }
        out += ']';
    }

    static void Summary(string &out, const CoreSummary &s) {
        if (s.unknown) { out += "[\"summary_unknown\"]"; return; }
        out += "[\"summary\",";
        Targets(out, s.reads); out += ',';
        Targets(out, s.writes); out += ',';
        Targets(out, s.grows); out += ',';
        Targets(out, s.rebinds);
        Append(out, ",", (int)s.aborts, ",", (int)s.outputs, "]");
    }

    static void Roots(string &out, const vector<CoreRootRef> &rs) {
        out += '[';
        for (size_t i = 0; i < rs.size(); i++) {
            if (i) out += ',';
            static const char *tags[] = { "r_local", "r_global", "r_param" };
            Append(out, "[\"", tags[rs[i].kind], "\",", rs[i].index, "]");
        }
        out += ']';
    }

    void Context(string &out, const CoreContext &c) {
        out += "[\"context\",";
        Append(out, c.impl, ",");
        Str(out, c.declkey);
        out += ",[";
        for (size_t i = 0; i < c.varroots.size(); i++) {
            if (i) out += ',';
            Append(out, "[\"vr\",", c.varroots[i].first, ",");
            Roots(out, c.varroots[i].second);
            out += ']';
        }
        out += "],[";
        for (size_t i = 0; i < c.resultroots.size(); i++) {
            if (i) out += ',';
            Roots(out, c.resultroots[i]);
        }
        out += "]]";
    }

    void Block(string &out, const CoreBlock &b) {
        Append(out, "[\"block\",", b.scope, ",[");
        for (size_t i = 0; i < b.stmts.size(); i++) {
            if (i) out += ',';
            Stmt(out, b.stmts[i]);
        }
        out += "],[";
        if (b.value) Expr(out, *b.value);
        out += "]]";
    }

    void Stmt(string &out, const CoreStmt &s) {
        switch (s.kind) {
            case CoreStmtKind::Let:
                Append(out, "[\"s_let\",", s.var, ",");
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::Assign:
                out += "[\"s_assign\",";
                Place(out, *s.place); out += ',';
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::AssignOp:
                Append(out, "[\"s_assign_op\",\"", CoreBinOpName(s.bin), "\",");
                Place(out, *s.place); out += ',';
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::Rebind:
                Append(out, "[\"s_rebind\",", s.var, ",");
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::Expr:
                out += "[\"s_expr\",";
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::Append:
                out += "[\"s_append\",";
                Place(out, *s.place); out += ',';
                View(out, *s.view);
                break;
            case CoreStmtKind::If:
                out += "[\"s_if\",";
                Expr(out, *s.expr); out += ',';
                Block(out, *s.then);
                out += ",[";
                if (s.otherwise) Block(out, *s.otherwise);
                out += ']';
                break;
            case CoreStmtKind::While:
                out += "[\"s_while\",";
                Expr(out, *s.expr); out += ',';
                Block(out, *s.then);
                break;
            case CoreStmtKind::ForRange:
                Append(out, "[\"s_for_range\",", s.var, ",");
                Expr(out, *s.expr); out += ',';
                Expr(out, *s.expr2); out += ',';
                Block(out, *s.then);
                break;
            case CoreStmtKind::ForEach:
                Append(out, "[\"s_for_each\",", s.var, ",[");
                if (s.index >= 0) Append(out, s.index);
                out += "],";
                View(out, *s.view);
                Append(out, ",", (int)s.byRef, ",");
                Block(out, *s.then);
                break;
            case CoreStmtKind::Ret:
                out += "[\"s_ret\",[";
                if (s.expr) Expr(out, *s.expr);
                out += ']';
                break;
            case CoreStmtKind::Break: out += "[\"s_break\""; break;
            case CoreStmtKind::Continue: out += "[\"s_continue\""; break;
            case CoreStmtKind::Print:
                out += "[\"s_print\",[";
                for (size_t i = 0; i < s.print.size(); i++) {
                    if (i) out += ',';
                    if (s.print[i].text) {
                        out += "[\"pa_text\",";
                        Str(out, s.print[i].str);
                    } else {
                        out += "[\"pa_expr\",";
                        Expr(out, *s.print[i].expr);
                    }
                    out += ']';
                }
                out += ']';
                break;
            case CoreStmtKind::Assert:
                out += "[\"s_assert\",";
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::Abort:
                out += "[\"s_abort\",";
                Str(out, s.message);
                break;
            case CoreStmtKind::Exit:
                out += "[\"s_exit\",";
                Expr(out, *s.expr);
                break;
        }
        Append(out, ",", O(s.org), "]");
    }

    void Place(string &out, const CorePlace &p) {
        switch (p.kind) {
            case CorePlace::Local: Append(out, "[\"p_local\",", p.index, "]"); break;
            case CorePlace::Global: Append(out, "[\"p_global\",", p.index, "]"); break;
            case CorePlace::Deref:
                out += "[\"p_deref\",";
                Expr(out, *p.expr);
                out += ']';
                break;
            case CorePlace::Elem:
                out += "[\"p_elem\",";
                View(out, *p.view); out += ',';
                Expr(out, *p.expr);
                Append(out, ",", O(p.org), "]");
                break;
        }
    }

    void View(string &out, const CoreView &v) {
        if (v.kind == CoreView::Of) {
            out += "[\"v_of\",";
            Place(out, *v.place);
        } else {
            out += "[\"v_val\",";
            Expr(out, *v.expr);
        }
        out += ']';
    }

    void Bound(string &out, const CoreBound &b) {
        switch (b.kind) {
            case CoreBound::None: out += "[\"b_none\"]"; return;
            case CoreBound::Expr: out += "[\"b_expr\","; break;
            case CoreBound::End: out += "[\"b_end\","; break;
        }
        Expr(out, *b.expr);
        out += ']';
    }

    void Expr(string &out, const CoreExpr &e) {
        switch (e.kind) {
            case CoreExprKind::Lit:
                Append(out, "[\"e_lit\",", T(e.type), ",\"", e.value, "\"]");
                break;
            case CoreExprKind::Bool: Append(out, "[\"e_bool\",", (int)e.flag, "]"); break;
            case CoreExprKind::Read:
                out += "[\"e_read\",";
                Place(out, *e.place);
                out += ']';
                break;
            case CoreExprKind::Ref:
                Append(out, "[\"e_ref\",\"", CoreMutName(e.mut), "\",");
                Place(out, *e.place);
                out += ']';
                break;
            case CoreExprKind::Slice:
                Append(out, "[\"e_slice\",\"", CoreMutName(e.mut), "\",");
                View(out, *e.view); out += ',';
                Bound(out, e.lo); out += ',';
                Bound(out, e.hi);
                Append(out, ",", O(e.org), "]");
                break;
            case CoreExprKind::Len:
                out += "[\"e_len\",";
                View(out, *e.view);
                out += ']';
                break;
            case CoreExprKind::Un:
                Append(out, "[\"e_un\",\"", CoreUnOpName(e.un), "\",");
                Expr(out, *e.a);
                Append(out, ",", O(e.org), "]");
                break;
            case CoreExprKind::Bin:
                Append(out, "[\"e_bin\",\"", CoreBinOpName(e.bin), "\",");
                Expr(out, *e.a); out += ',';
                Expr(out, *e.b);
                Append(out, ",", O(e.org), "]");
                break;
            case CoreExprKind::Cmp:
                Append(out, "[\"e_cmp\",\"", CoreCmpOpName(e.cmp), "\",");
                Expr(out, *e.a); out += ',';
                Expr(out, *e.b);
                out += ']';
                break;
            case CoreExprKind::And:
            case CoreExprKind::Or:
                out += e.kind == CoreExprKind::And ? "[\"e_and\"," : "[\"e_or\",";
                Expr(out, *e.a); out += ',';
                Expr(out, *e.b);
                out += ']';
                break;
            case CoreExprKind::Not:
                out += "[\"e_not\",";
                Expr(out, *e.a);
                out += ']';
                break;
            case CoreExprKind::Conv:
                Append(out, "[\"e_conv\",\"", CoreConvKindName(e.conv), "\",", T(e.type), ",");
                Expr(out, *e.a);
                Append(out, ",", O(e.org), "]");
                break;
            case CoreExprKind::Call:
                Append(out, "[\"e_call\",", e.ctx, ",[");
                for (size_t i = 0; i < e.args.size(); i++) {
                    if (i) out += ',';
                    auto &a = e.args[i];
                    if (a.kind == CoreArg::Val) {
                        out += "[\"a_val\",";
                        Expr(out, *a.expr);
                    } else {
                        Append(out, "[\"a_ref\",\"", CoreMutName(a.mut), "\",");
                        Place(out, *a.place);
                    }
                    out += ']';
                }
                Append(out, "],", O(e.org), "]");
                break;
            case CoreExprKind::Push:
                out += "[\"e_push\",";
                Place(out, *e.place); out += ',';
                Expr(out, *e.a);
                out += ']';
                break;
            case CoreExprKind::If:
                out += "[\"e_if\",";
                Expr(out, *e.a); out += ',';
                Block(out, *e.then); out += ',';
                Block(out, *e.otherwise);
                out += ']';
                break;
            case CoreExprKind::Block:
                out += "[\"e_block\",";
                Block(out, *e.then);
                out += ']';
                break;
            case CoreExprKind::Arr:
                Append(out, "[\"e_arr\",", T(e.type), ",[");
                for (size_t i = 0; i < e.elems.size(); i++) {
                    if (i) out += ',';
                    Expr(out, *e.elems[i]);
                }
                out += "]]";
                break;
            case CoreExprKind::Fill:
                Append(out, "[\"e_fill\",", T(e.type), ",");
                Expr(out, *e.a);
                out += ']';
                break;
        }
    }
};

}  // namespace goose
