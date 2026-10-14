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
        typenum.clear();
        typeorder.clear();
        origins.clear();
        originnum.clear();
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
        if (CoreHasShrink(m.profile))
            for (size_t i = 0; i < m.types.size(); i++)
                if (m.types[i].kind == CoreType::Struct) T((int)i);
        // Files are numbered by first use in the origin table.
        filemap.assign(m.files.size(), -1);
        fileorder.clear();
        for (auto &o : origins) {
            if (filemap[o.file] < 0) {
                filemap[o.file] = (int)fileorder.size();
                fileorder.push_back(o.file);
            }
        }
        string out = cat("[\"module\",\"", CORE_SCHEMA, "\",\"", CoreProfileName(m.profile), "\",[");
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
        out += ']';
        if (CoreHasShrink(m.profile)) {
            out += ",[";
            for (size_t i = 0; i < m.structs.size(); i++) {
                if (i) out += ',';
                StructRecord(out, m.structs[i]);
            }
            out += ']';
        }
        if (CoreHasConstruction(m.profile)) {
            out += ",[";
            for (size_t i = 0; i < m.targets.size(); i++) {
                if (i) out += ',';
                out += "[\"target\",";
                Ids(out, m.targets[i].members);
                out += ']';
            }
            out += ']';
        }
        out += ',';
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
    // The diagnostic paths in output order.
    vector<string> DiagFileTable() const {
        vector<string> out;
        for (auto f : fileorder) out.push_back(f < (int)m.diagfiles.size() ? m.diagfiles[f] : m.files[f]);
        return out;
    }
    vector<string> FileModuleTable() const {
        vector<string> out;
        for (auto f : fileorder) out.push_back(f < (int)m.filemodules.size() ? m.filemodules[f] : string());
        return out;
    }
    // Each origin with its file as numbered in the output.
    vector<CoreOrigin> OriginTable() const {
        auto out = origins;
        for (auto &o : out) o.file = filemap[o.file];
        return out;
    }
    // The number of an origin of this module.
    CoreOriginId OriginId(const CoreOrigin &o) const {
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
        if (t.kind == CoreType::Struct) {
            for (auto &field : m.structs[t.structid].fields) T(field.type);
        } else if (t.elem >= 0) {
            T(t.elem);
        }
        for (auto part : t.parts) T(part);
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
            case CoreType::VarArr: Append(out, "[\"varr\",", typenum.at(t.elem), "]"); break;
            case CoreType::Grow: Append(out, "[\"grow\",", typenum.at(t.elem), "]"); break;
            case CoreType::GrowShrink: Append(out, "[\"growshrink\",", typenum.at(t.elem), "]"); break;
            case CoreType::Limited: Append(out, "[\"limited\",", typenum.at(t.elem), ",", t.count, "]"); break;
            case CoreType::Ref:
                Append(out, "[\"ref\",\"", CoreMutName(t.mut), "\",", typenum.at(t.elem), "]");
                break;
            case CoreType::Slice:
                Append(out, "[\"slice\",\"", CoreMutName(t.mut), "\",", typenum.at(t.elem), "]");
                break;
            case CoreType::View:
                Append(out, "[\"view\",\"", CoreMutName(t.mut), "\",", typenum.at(t.elem), "]");
                break;
            case CoreType::Ptr: out += "[\"ptr\"]"; break;
            case CoreType::Tuple:
                out += "[\"tuple\",[";
                for (size_t i = 0; i < t.parts.size(); i++) {
                    if (i) out += ',';
                    Append(out, typenum.at(t.parts[i]));
                }
                out += "]]";
                break;
            case CoreType::Struct: Append(out, "[\"struct\",", t.structid, "]"); break;
            case CoreType::Dest: case CoreType::Built: case CoreType::Cancelled:
                throw CompileError { "internal compiler error: Core contains a GIR construction carrier" };
        }
    }

    void StructRecord(string &out, const CoreStruct &s) {
        Append(out, "[\"struct_def\",", s.size, ",[" );
        for (size_t i = 0; i < s.fields.size(); i++) {
            if (i) out += ',';
            auto &field = s.fields[i];
            Append(out, "[\"field\",", typenum.at(field.type), ",\"",
                   field.binding == CoreVarKind::Var ? "var" : "let", "\",\"",
                   CoreMutName(field.contents), "\",", field.offset, "]");
        }
        out += "]]";
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
            auto &result = im.results[i];
            if (CoreHasConstruction(m.profile)) {
                Append(out, "[\"result\",", T(result.type), ",\"", CoreRequestName(result.request), "\",[");
                if (result.namedLocal) Append(out, *result.namedLocal);
                out += "]]";
            } else Append(out, T(result.type));
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

    static void Ids(string &out, const vector<int> &ids) {
        out += '[';
        for (size_t i = 0; i < ids.size(); i++) {
            if (i) out += ',';
            Append(out, ids[i]);
        }
        out += ']';
    }

    void PrintArg(string &out, const CorePrintArg &arg) {
        switch (arg.kind) {
            case CorePrintArg::Text:
                out += "[\"pa_text\",";
                Str(out, arg.str);
                break;
            case CorePrintArg::Expr:
                out += "[\"pa_expr\",";
                Expr(out, *arg.expr);
                break;
            case CorePrintArg::View:
                out += "[\"pa_view\",";
                View(out, *arg.view);
                break;
        }
        out += ']';
    }

    void PrintArgs(string &out, const vector<CorePrintArg> &args) {
        out += '[';
        for (size_t i = 0; i < args.size(); i++) {
            if (i) out += ',';
            PrintArg(out, args[i]);
        }
        out += ']';
    }

    void Summary(string &out, const CoreSummary &s) {
        if (s.unknown) { out += "[\"summary_unknown\"]"; return; }
        out += "[\"summary\",";
        Targets(out, s.reads); out += ',';
        Targets(out, s.writes); out += ',';
        Targets(out, s.grows); out += ',';
        if (CoreHasShrink(m.profile)) {
            Targets(out, s.shrinks); out += ',';
        }
        Targets(out, s.rebinds);
        if (CoreHasConstruction(m.profile)) {
            out += ',';
            Ids(out, s.constructs); out += ',';
            Ids(out, s.needs); out += ',';
            Ids(out, s.escapes);
        }
        Append(out, ",", (int)s.aborts, ",", (int)s.outputs, "]");
    }

    static void Roots(string &out, const vector<CoreRootRef> &rs) {
        out += '[';
        for (size_t i = 0; i < rs.size(); i++) {
            if (i) out += ',';
            if (rs[i].kind == CoreRootRef::Static) out += "[\"r_static\"]";
            else {
                static const char *tags[] = { "r_static", "r_local", "r_global", "r_param" };
                Append(out, "[\"", tags[rs[i].kind], "\",", rs[i].index, "]");
            }
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
            if (i < c.hascontent.size() && c.hascontent[i]) {
                out += ',';
                Roots(out, c.content[i]);
            }
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
            case CoreStmtKind::AssignWhole:
                out += "[\"s_assign_whole\",";
                Place(out, *s.place); out += ',';
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::PopN:
                out += "[\"s_pop_n\",";
                Place(out, *s.place); out += ',';
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::Resize:
                out += "[\"s_resize\",";
                Place(out, *s.place); out += ',';
                Expr(out, *s.expr); out += ",[";
                if (s.expr2) Expr(out, *s.expr2);
                out += ']';
                break;
            case CoreStmtKind::Clear:
                out += "[\"s_clear\",";
                Place(out, *s.place);
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
                out += "[\"s_print\",";
                PrintArgs(out, s.print);
                break;
            case CoreStmtKind::Receive:
                out += "[\"s_receive\",[";
                for (size_t i = 0; i < s.vars.size(); i++) {
                    if (i) out += ',';
                    Append(out, s.vars[i]);
                }
                out += "],";
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::AppendValue:
            case CoreStmtKind::AppendConstruct:
                out += s.kind == CoreStmtKind::AppendValue ? "[\"s_append_value\"," : "[\"s_append_construct\",";
                Place(out, *s.place); out += ',';
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::RetValues:
                out += "[\"s_ret_values\",[";
                for (size_t i = 0; i < s.values.size(); i++) {
                    if (i) out += ',';
                    Expr(out, *s.values[i]);
                }
                out += ']';
                break;
            case CoreStmtKind::RetForward:
                out += "[\"s_ret_forward\",";
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::ReturnFrom:
                Append(out, "[\"s_return_from\",", s.target, ",[");
                for (size_t i = 0; i < s.values.size(); i++) {
                    if (i) out += ',';
                    Expr(out, *s.values[i]);
                }
                out += ']';
                break;
            case CoreStmtKind::ReturnFromForward:
                Append(out, "[\"s_return_from_forward\",", s.target, ",");
                Expr(out, *s.expr);
                break;
            case CoreStmtKind::BreakValue:
                out += "[\"s_break_value\",";
                Expr(out, *s.expr);
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
            case CorePlace::Field:
                out += "[\"p_field\",";
                Place(out, *p.base);
                Append(out, ",", p.index, "]");
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
                    visit([&](auto &arg) {
                        using Arg = decay_t<decltype(arg)>;
                        if constexpr (is_same_v<Arg, CoreArgValue>) {
                            out += "[\"a_val\",";
                            Expr(out, *arg.expr);
                        } else if constexpr (is_same_v<Arg, CoreArgConstruct>) {
                            out += "[\"a_construct\",";
                            Expr(out, *arg.expr);
                        } else {
                            Append(out, "[\"a_ref\",\"", CoreMutName(arg.mut), "\",");
                            Place(out, *arg.place);
                        }
                        out += ']';
                    }, a);
                }
                Append(out, "],", O(e.org), "]");
                break;
            case CoreExprKind::Push:
                out += "[\"e_push\",";
                Place(out, *e.place); out += ',';
                Expr(out, *e.a);
                if (CoreHasShrink(m.profile)) Append(out, ",", O(e.org));
                out += ']';
                break;
            case CoreExprKind::Pop:
                out += "[\"e_pop\",";
                Place(out, *e.place);
                Append(out, ",", O(e.org), "]");
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
            case CoreExprKind::Struct:
                Append(out, "[\"e_struct\",", T(e.type), ",[" );
                for (size_t i = 0; i < e.elems.size(); i++) {
                    if (i) out += ',';
                    Expr(out, *e.elems[i]);
                }
                out += "]]";
                break;
            case CoreExprKind::Bytes:
                Append(out, "[\"e_bytes\",", T(e.type), ",[" );
                for (size_t i = 0; i < e.bytes.size(); i++) {
                    if (i) out += ',';
                    Append(out, (unsigned)e.bytes[i]);
                }
                Append(out, "],", O(e.org), "]");
                break;
            case CoreExprKind::String:
                Append(out, "[\"e_str\",", T(e.type), ",");
                PrintArgs(out, e.print);
                Append(out, ",", O(e.org), "]");
                break;
            case CoreExprKind::Copy:
                Append(out, "[\"e_copy\",", T(e.type), ",");
                Place(out, *e.place);
                Append(out, ",", O(e.org), "]");
                break;
            case CoreExprKind::ResultLocal:
                Append(out, "[\"e_result_local\",", e.var, ",", O(e.org), "]");
                break;
            case CoreExprKind::Values:
                out += "[\"e_values\",[";
                for (size_t i = 0; i < e.values.size(); i++) {
                    if (i) out += ',';
                    Expr(out, *e.values[i]);
                }
                out += "]]";
                break;
        }
    }
};

}  // namespace goose
