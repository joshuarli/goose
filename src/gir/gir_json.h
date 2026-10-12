// Goose compiler — GIR-H, serialization (schema gir-h/0.2).
//
// Records are tagged arrays as in the Core encoding. The file and origin
// tables are the Core module's, unchanged; the type table is numbered by first
// mention in document order, so the globals and functions are written first,
// interning types as they are met, and the table they built is put in front.
#pragma once

namespace goose {

inline constexpr const char *GIR_SCHEMA = "gir-h/0.2";

class GirWriter {
public:
    explicit GirWriter(const GirModule &module) : m(module) {}

    string Write() {
        string objs = "[";
        for (size_t i = 0; i < m.globals.size(); i++) {
            if (i) objs += ',';
            Global(objs, m.globals[i]);
        }
        objs += "],[";
        for (size_t i = 0; i < m.funcs.size(); i++) {
            if (i) objs += ',';
            Func(objs, m.funcs[i]);
        }
        objs += ']';
        string out = cat("[\"module\",\"", GIR_SCHEMA, "\",\"", CORE_PROFILE, "\",[");
        for (size_t i = 0; i < m.files.size(); i++) {
            if (i) out += ',';
            out += "[\"file\",";
            Str(out, m.files[i]);
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
        for (size_t i = 0; i < m.origins.size(); i++) {
            if (i) out += ',';
            Append(out, "[\"origin\",", m.origins[i].file, ",", m.origins[i].line, ",\"",
                   CoreOriginKindName(m.origins[i].kind), "\"]");
        }
        out += "]]\n";
        return out;
    }

private:
    const GirModule &m;
    unordered_map<GirTypeId, int> typenum;
    vector<GirTypeId> typeorder;

    int T(GirTypeId id) {
        if (auto it = typenum.find(id); it != typenum.end()) return it->second;
        auto &t = m.types[id];
        if (t.elem >= 0) T(t.elem);
        auto n = (int)typeorder.size();
        typenum[id] = n;
        typeorder.push_back(id);
        return n;
    }

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

    static void Ints(string &out, const vector<int> &v) {
        out += '[';
        for (size_t i = 0; i < v.size(); i++) {
            if (i) out += ',';
            Append(out, v[i]);
        }
        out += ']';
    }

    static void OptOrg(string &out, int org) {
        if (org < 0) out += "[]";
        else Append(out, "[", org, "]");
    }

    void Global(string &out, const GirGlobal &g) {
        out += "[\"global\",";
        Str(out, g.name);
        Append(out, ",", T(g.ty), ",\"", g.kind == CoreVarKind::Var ? "var" : "let", "\",");
        Func(out, g.init);
        Append(out, ",", g.org, "]");
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

    void Func(string &out, const GirFunc &f) {
        out += "[\"func\",";
        Str(out, f.name);
        out += ",[";
        for (size_t i = 0; i < f.params.size(); i++) {
            if (i) out += ',';
            Append(out, T(f.params[i]));
        }
        out += "],[";
        for (size_t i = 0; i < f.results.size(); i++) {
            if (i) out += ',';
            Append(out, T(f.results[i]));
        }
        out += "],[";
        for (size_t i = 0; i < f.slots.size(); i++) {
            if (i) out += ',';
            auto &s = f.slots[i];
            Append(out, "[\"slot\",", T(s.ty), ",\"", s.kind == CoreVarKind::Var ? "var" : "let", "\",",
                   s.scope, ",", s.var, "]");
        }
        out += "],[";
        for (size_t i = 0; i < f.scopes.size(); i++) {
            if (i) out += ',';
            if (f.scopes[i] < 0) out += "[\"scope\",[]]";
            else Append(out, "[\"scope\",[", f.scopes[i], "]]");
        }
        out += "],[";
        for (size_t i = 0; i < f.blocks.size(); i++) {
            if (i) out += ',';
            Block(out, f.blocks[i]);
        }
        out += "],";
        Summary(out, f.summary);
        out += ',';
        OptOrg(out, f.org);
        out += ']';
    }

    void Block(string &out, const GirBlock &b) {
        out += "[\"block\",[";
        for (size_t i = 0; i < b.params.size(); i++) {
            if (i) out += ',';
            Append(out, "[\"bp\",", b.params[i].first, ",", T(b.params[i].second), "]");
        }
        out += "],[";
        for (size_t i = 0; i < b.insts.size(); i++) {
            if (i) out += ',';
            Inst(out, b.insts[i]);
        }
        out += "]]";
    }

    static void Bound(string &out, const GirBound &b) {
        switch (b.kind) {
            case GirBound::None: out += "[\"bd_none\"]"; break;
            case GirBound::Val: Append(out, "[\"bd_val\",", b.val, "]"); break;
            case GirBound::End: Append(out, "[\"bd_end\",", b.val, "]"); break;
        }
    }

    void Inst(string &out, const GirInst &i) {
        auto def = [&](const char *tag) { Append(out, "[\"", tag, "\",", i.res); };
        switch (i.op) {
            case GirOp::Int: def("i_int"); Append(out, ",", T(i.ty), ",\"", i.text, "\"]"); return;
            case GirOp::Bool: def("i_bool"); Append(out, ",", (int)i.flag, "]"); return;
            case GirOp::Unit: def("i_unit"); out += ']'; return;
            case GirOp::Bin:
                def("i_bin");
                Append(out, ",\"", CoreBinOpName(i.bin), "\",", T(i.ty), ",", i.a, ",", i.b, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Un:
                def("i_un");
                Append(out, ",\"", CoreUnOpName(i.un), "\",", T(i.ty), ",", i.a, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Cmp:
                def("i_cmp");
                Append(out, ",\"", CoreCmpOpName(i.cmp), "\",", T(i.ty), ",", i.a, ",", i.b, "]");
                return;
            case GirOp::BoolCmp:
                def("i_bcmp");
                Append(out, ",\"", CoreCmpOpName(i.cmp), "\",", i.a, ",", i.b, "]");
                return;
            case GirOp::Not: def("i_not"); Append(out, ",", i.a, "]"); return;
            case GirOp::Conv:
                def("i_conv");
                {
                    auto src = T(i.ty);   // Mentioned in this order.
                    auto dst = T(i.ty2);
                    Append(out, ",\"", CoreConvKindName(i.conv), "\",", src, ",", dst, ",", i.a, ",");
                }
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Next: def("i_next"); Append(out, ",", T(i.ty), ",", i.a, "]"); return;
            case GirOp::Slot: def("i_slot"); Append(out, ",", i.idx, "]"); return;
            case GirOp::Global: def("i_global"); Append(out, ",", i.idx, "]"); return;
            case GirOp::Elem: def("i_elem"); Append(out, ",", i.a, ",", i.b, "]"); return;
            case GirOp::Freeze: def("i_freeze"); Append(out, ",", i.a, "]"); return;
            case GirOp::Load: def("i_load"); Append(out, ",", i.a, "]"); return;
            case GirOp::Snap: def("i_snap"); Append(out, ",", i.a, "]"); return;
            case GirOp::SliceView: def("i_sview"); Append(out, ",", i.a, "]"); return;
            case GirOp::ViewLen: def("i_vlen"); Append(out, ",", i.a, "]"); return;
            case GirOp::ViewSlice:
                def("i_vslice");
                Append(out, ",\"", CoreMutName(i.mut), "\",", i.a, ",");
                Bound(out, i.lo);
                out += ',';
                Bound(out, i.hi);
                out += ',';
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::ArrayLen: def("i_alen"); Append(out, ",", i.a, "]"); return;
            case GirOp::Index:
                def("i_index");
                Append(out, ",", i.a, ",", i.b, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Push:
                def("i_push");
                Append(out, ",", i.a, ",", i.b, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Call:
                def("i_call");
                Append(out, ",", i.idx, ",");
                Ints(out, i.vals);
                out += ',';
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Arr:
                def("i_arr");
                Append(out, ",", T(i.ty), ",");
                Ints(out, i.vals);
                out += ']';
                return;
            case GirOp::Fill: def("i_fill"); Append(out, ",", T(i.ty), ",", i.a, "]"); return;
            case GirOp::Init:
                Append(out, "[\"x_init\",", i.idx, ",", i.a, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Store:
                Append(out, "[\"x_store\",", i.a, ",", i.b, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Append:
                Append(out, "[\"x_append\",", i.a, ",", i.b, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Enter: Append(out, "[\"x_enter\",", i.idx, "]"); return;
            case GirOp::Leave: Append(out, "[\"x_leave\",", i.idx, "]"); return;
            case GirOp::Print:
                out += "[\"x_print\",[";
                for (size_t k = 0; k < i.parts.size(); k++) {
                    if (k) out += ',';
                    if (i.parts[k].text) {
                        out += "[\"pp_text\",";
                        Str(out, i.parts[k].str);
                        out += ']';
                    } else {
                        Append(out, "[\"pp_val\",", i.parts[k].val, "]");
                    }
                }
                out += "],";
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Br:
                Append(out, "[\"t_br\",", i.idx, ",");
                Ints(out, i.vals);
                out += ']';
                return;
            case GirOp::CondBr:
                Append(out, "[\"t_condbr\",", i.a, ",", i.idx, ",");
                Ints(out, i.vals);
                Append(out, ",", i.idx2, ",");
                Ints(out, i.vals2);
                out += ']';
                return;
            case GirOp::Ret:
                out += "[\"t_ret\",";
                Ints(out, i.vals);
                out += ',';
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Abort:
                Append(out, "[\"t_abort\",\"", GirAbortKindName(i.abort), "\",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Exit:
                Append(out, "[\"t_exit\",", i.a, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
        }
    }
};

}  // namespace goose
