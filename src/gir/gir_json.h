// Goose compiler — GIR-H, serialization (schema gir-h/0.4).
//
// Records are tagged arrays as in the Core encoding. The file and origin
// tables are the Core module's, unchanged; the type table is numbered by first
// mention in document order, so the globals and functions are written first,
// interning types as they are met, and the table they built is put in front.
#pragma once

namespace goose {

inline constexpr const char *GIR_SCHEMA = "gir-h/0.4";

class GirWriter {
public:
    explicit GirWriter(const GirModule &module) : m(module) {}

    string Write() {
        typenum.clear();
        typeorder.clear();
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
        if (CoreHasShrink(m.profile))
            for (size_t i = 0; i < m.types.size(); i++)
                if (m.types[i].kind == CoreType::Struct) T((int)i);
        string out = cat("[\"module\",\"", GIR_SCHEMA, "\",\"", CoreProfileName(m.profile), "\",[");
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
                Ints(out, m.targets[i].members);
                out += ']';
            }
            out += ']';
        }
        out += ',';
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

    // The low stage (schema gir-l/0.2): the same style, written but not read.
    string WriteLow() {
        typenum.clear();
        typeorder.clear();
        string objs = "[";
        for (size_t i = 0; i < m.lowglobals.size(); i++) {
            if (i) objs += ',';
            auto &g = m.lowglobals[i];
            objs += "[\"lglobal\",";
            Str(objs, g.name);
            if (g.kind == GirMember::Scalar) Append(objs, ",\"scalar\",", T(g.ty), "]");
            else if (g.kind == GirMember::Bytes) Append(objs, ",\"bytes\",", g.size, "]");
            else objs += ",\"header\"]";
        }
        objs += "],[";
        for (size_t i = 0; i < m.funcs.size(); i++) {
            if (i) objs += ',';
            LowFunc(objs, m.funcs[i]);
        }
        objs += ']';
        string out = cat("[\"module\",\"gir-l/0.2\",\"", CoreProfileName(m.profile), "\",[");
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
        out += ']';
        if (CoreHasConstruction(m.profile)) {
            out += ",[";
            for (size_t i = 0; i < m.lowtargets.size(); i++) {
                if (i) out += ',';
                out += "[\"ltarget\",";
                Ints(out, m.lowtargets[i].members);
                out += ",[],[]]";
            }
            out += ']';
        }
        out += ',';
        out += objs;
        Append(out, ",", m.entry, ",");
        Ints(out, m.initfuncs);
        Append(out, ",", m.mainstacks, ",", m.globalstacks);
        if (CoreHasConstruction(m.profile)) Append(out, ",", m.pointerBytes);
        out += ",[";
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
    const GirFunc *function = nullptr;

    int T(GirTypeId id) {
        if (auto it = typenum.find(id); it != typenum.end()) return it->second;
        auto &t = m.types[id];
        if (t.kind == CoreType::Struct) {
            for (auto &field : m.structs[t.structid].fields) T(field.type);
        } else if (t.elem >= 0) {
            T(t.elem);
        }
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
            case CoreType::Struct: Append(out, "[\"struct\",", t.structid, "]"); break;
            case CoreType::Dest:
                Append(out, "[\"dest\",", typenum.at(t.elem), ",\"", CoreRequestName(t.request), "\"]");
                break;
            case CoreType::Built:
                Append(out, "[\"built\",", typenum.at(t.elem), ",\"", CoreRequestName(t.request), "\"]");
                break;
            case CoreType::Cancelled:
                Append(out, "[\"cancelled\",", typenum.at(t.elem), ",\"", CoreRequestName(t.request), "\"]");
                break;
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

    static void Summary(string &out, const CoreSummary &s, CoreProfile profile) {
        if (s.unknown) { out += "[\"summary_unknown\"]"; return; }
        out += "[\"summary\",";
        Targets(out, s.reads); out += ',';
        Targets(out, s.writes); out += ',';
        Targets(out, s.grows); out += ',';
        if (CoreHasShrink(profile)) {
            Targets(out, s.shrinks); out += ',';
        }
        if (CoreHasConstruction(profile)) {
            Ints(out, s.constructs); out += ',';
            Ints(out, s.needs); out += ',';
            Ints(out, s.escapes); out += ',';
        }
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

    static void RootRows(string &out, const vector<pair<int, vector<CoreRootRef>>> &rows, const char *tag) {
        out += '[';
        for (size_t i = 0; i < rows.size(); i++) {
            if (i) out += ',';
            Append(out, "[\"", tag, "\",", rows[i].first, ",");
            Roots(out, rows[i].second);
            out += ']';
        }
        out += ']';
    }

    static void RootInfo(string &out, const GirRootInfo &r) {
        out += "[\"roots\",";
        RootRows(out, r.params, "vr");
        out += ',';
        RootRows(out, r.contents, "cr");
        out += ",[";
        for (size_t i = 0; i < r.results.size(); i++) {
            if (i) out += ',';
            Roots(out, r.results[i]);
        }
        out += "]]";
    }

    static void Fact(string &out, const GirFact &fact) {
        switch (fact.kind) {
            case GirFact::Ge0: Append(out, "[\"f_ge0\",", fact.a, "]"); return;
            case GirFact::Lt: Append(out, "[\"f_lt\",", fact.a, ",", fact.b, "]"); return;
            case GirFact::LenGe:
                Append(out, "[\"f_len_ge\",", fact.a, ",", fact.b, "]");
                return;
            case GirFact::ViewLenGe:
                Append(out, "[\"f_view_len_ge\",", fact.a, ",", fact.b, "]");
                return;
        }
    }

    static void Certificate(string &out, const optional<GirFactCertificate> &certificate) {
        if (!certificate) {
            out += "[]";
            return;
        }
        out += "[[\"certificate\",[";
        for (size_t block = 0; block < certificate->blocks.size(); block++) {
            if (block) out += ',';
            out += '[';
            for (size_t fact = 0; fact < certificate->blocks[block].size(); fact++) {
                if (fact) out += ',';
                Fact(out, certificate->blocks[block][fact]);
            }
            out += ']';
        }
        out += "]]]";
    }

    void Func(string &out, const GirFunc &f) {
        auto previousFunction = function;
        function = &f;
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
            if (CoreHasConstruction(m.profile))
                Append(out, "[\"result\",", T(f.results[i]), ",\"register\",[]]");
            else
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
        function = previousFunction;
        RootInfo(out, f.roots);
        out += ',';
        Summary(out, f.summary, m.profile);
        out += ',';
        OptOrg(out, f.org);
        out += ',';
        Certificate(out, f.certificate);
        out += ']';
    }

    void LowFunc(string &out, const GirFunc &f) {
        out += "[\"lfunc\",";
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
        Append(out, "],", f.stacks, ",[");
        for (size_t i = 0; i < f.members.size(); i++) {
            if (i) out += ',';
            auto &mem = f.members[i];
            if (mem.kind == GirMember::Scalar) Append(out, "[\"m_scalar\",", T(mem.ty), ",");
            else if (mem.kind == GirMember::Bytes) Append(out, "[\"m_bytes\",", mem.size, ",");
            else Append(out, "[\"m_header\",", mem.stack, ",");
            Append(out, mem.scope, ",");
            Str(out, mem.name);
            out += ']';
        }
        out += "],[";
        for (size_t i = 0; i < f.scopes.size(); i++) {
            if (i) out += ',';
            Append(out, f.scopes[i]);
        }
        out += "],[";
        for (size_t i = 0; i < f.blocks.size(); i++) {
            if (i) out += ',';
            auto &b = f.blocks[i];
            out += "[\"block\",[";
            for (size_t k = 0; k < b.params.size(); k++) {
                if (k) out += ',';
                Append(out, "[\"bp\",", b.params[k].first, ",", T(b.params[k].second), "]");
            }
            out += "],[";
            for (size_t k = 0; k < b.insts.size(); k++) {
                if (k) out += ',';
                LowInst(out, b.insts[k]);
            }
            out += "]]";
        }
        out += "]]";
    }

    void LowInst(string &out, const GirInst &i) {
        auto def = [&](const char *tag) { Append(out, "[\"", tag, "\",", i.res); };
        switch (i.op) {
            case GirOp::Int: def("i_int"); Append(out, ",", T(i.ty), ",\"", i.text, "\"]"); return;
            case GirOp::Bool: def("i_bool"); Append(out, ",", (int)i.flag, "]"); return;
            case GirOp::Bin:
                def("i_bin");
                Append(out, ",\"", CoreBinOpName(i.bin), "\",", T(i.ty), ",", i.a, ",", i.b, ",", (int)i.flag, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Un:
                def("i_un");
                Append(out, ",\"", CoreUnOpName(i.un), "\",", T(i.ty), ",", i.a, ",", (int)i.flag, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Cmp:
                def("i_cmp");
                Append(out, ",\"", CoreCmpOpName(i.cmp), "\",", T(i.ty), ",", i.a, ",", i.b, "]");
                return;
            case GirOp::Not: def("i_not"); Append(out, ",", i.a, "]"); return;
            case GirOp::Conv: {
                def("i_conv");
                auto src = T(i.ty);
                auto dst = T(i.ty2);
                Append(out, ",\"", CoreConvKindName(i.conv), "\",", src, ",", dst, ",", i.a, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            }
            case GirOp::Call:
                def("i_call");
                Append(out, ",", i.idx, ",");
                Ints(out, i.vals);
                out += ',';
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::PtrOffset: def("l_offset"); Append(out, ",", i.a, ",", i.b, ",", i.idx, "]"); return;
            case GirOp::PLoad: def("l_load"); Append(out, ",", T(i.ty), ",", i.a, "]"); return;
            case GirOp::FrameAddr: def("l_frame"); Append(out, ",", i.idx, "]"); return;
            case GirOp::LocalGet: def("l_get"); Append(out, ",", i.idx, "]"); return;
            case GirOp::StackAt: def("l_stack"); Append(out, ",", i.a, ",", i.idx, "]"); return;
            case GirOp::StackMark: def("l_mark"); Append(out, ",", i.a, "]"); return;
            case GirOp::GlobalAddr: def("l_gaddr"); Append(out, ",", i.idx, "]"); return;
            case GirOp::GlobalStack: def("l_gstack"); Append(out, ",", i.idx, "]"); return;
            case GirOp::HdrBase: def("l_hbase"); Append(out, ",", i.a, "]"); return;
            case GirOp::HdrLen: def("l_hlen"); Append(out, ",", i.a, "]"); return;
            case GirOp::PStore: Append(out, "[\"l_store\",", T(i.ty), ",", i.a, ",", i.b, "]"); return;
            case GirOp::LocalSet: Append(out, "[\"l_set\",", i.idx, ",", i.a, "]"); return;
            case GirOp::StackRelease: Append(out, "[\"l_release\",", i.a, ",", i.b, "]"); return;
            case GirOp::StackBump: Append(out, "[\"l_bump\",", i.a, ",", i.b, ",", i.idx, "]"); return;
            case GirOp::HdrInit: Append(out, "[\"l_hinit\",", i.a, ",", i.b, "]"); return;
            case GirOp::HdrSetLen: Append(out, "[\"l_hsetlen\",", i.a, ",", i.b, "]"); return;
            case GirOp::BytesCopy: Append(out, "[\"l_copy\",", i.a, ",", i.b, ",", i.vals[0], "]"); return;
            case GirOp::BytesMove: Append(out, "[\"l_move\",", i.a, ",", i.b, ",", i.vals[0], "]"); return;
            case GirOp::BytesFill:
                Append(out, "[\"l_fill\",", i.a, ",", i.b, ",", i.idx, ",", i.vals[0], "]");
                return;
            case GirOp::RtCall:
                Append(out, "[\"l_rt\",\"", GirRtName(i.idx), "\",", i.a, ",");
                Str(out, i.text);
                out += ']';
                return;
            case GirOp::Abort:
                Append(out, "[\"t_abort\",\"", GirAbortKindName(i.abort), "\",");
                Ints(out, i.vals);
                out += ',';
                OptOrg(out, i.org);
                out += ',';
                Str(out, i.text);
                out += ']';
                return;
            default: Inst(out, i); return;   // Terminators and nothing else are shared as written.
        }
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
            NoteConstructionType(b.insts[i]);
            Inst(out, b.insts[i]);
        }
        out += "]]";
    }

    GirTypeId ConstructionType(CoreType::Kind kind, const GirInst &inst) const {
        CoreType type;
        type.kind = kind;
        if (inst.op == GirOp::DestOpen) {
            type.elem = inst.ty;
            type.request = inst.request;
        } else {
            if (!function)
                throw CompileError { "internal compiler error: construction result has no function" };
            const GirInst *open = nullptr;
            for (auto &block : function->blocks)
                for (auto &candidate : block.insts)
                    if (candidate.op == GirOp::DestOpen && candidate.res == inst.a) open = &candidate;
            if (!open)
                throw CompileError { "internal compiler error: construction completion has no destination" };
            type.elem = open->ty;
            type.request = open->request;
        }
        for (size_t id = 0; id < m.types.size(); id++)
            if (m.types[id] == type) return (GirTypeId)id;
        throw CompileError { "internal compiler error: construction result type was not verified" };
    }

    void NoteConstructionType(const GirInst &inst) {
        if (!CoreHasConstruction(m.profile)) return;
        if (inst.op == GirOp::DestOpen) T(ConstructionType(CoreType::Dest, inst));
        if (inst.op == GirOp::DestFinish) T(ConstructionType(CoreType::Built, inst));
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
            case GirOp::Snap:
                def("i_snap");
                Append(out, ",\"", i.snap == GirSnapshotMode::Owner ? "owner" : "borrowed", "\",", i.a, "]");
                return;
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
            case GirOp::IndexProven:
                def("i_index_proven");
                Append(out, ",", i.a, ",", i.b, "]");
                return;
            case GirOp::Push:
                def("i_push");
                Append(out, ",", i.a, ",", i.b, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Pop:
                def("i_pop");
                Append(out, ",", i.a, ",");
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
            case GirOp::Struct:
                def("i_struct");
                Append(out, ",", T(i.ty), ",");
                Ints(out, i.vals);
                out += ']';
                return;
            case GirOp::Field: def("i_field"); Append(out, ",", i.a, ",", i.idx, "]"); return;
            case GirOp::DestOpen:
                def("i_dest_open");
                Append(out, ",[\"dr_slot\",", i.idx, "],", T(i.ty), ",\"", CoreRequestName(i.request), "\",");
                if (i.knownCount) Append(out, "[", *i.knownCount, "]");
                else out += "[]";
                out += ',';
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::DestFinish:
                def("i_dest_finish");
                Append(out, ",", i.a, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
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
            case GirOp::PopN:
                Append(out, "[\"x_pop_n\",", i.a, ",", i.b, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Resize:
                Append(out, "[\"x_resize\",", i.a, ",", i.b, ",");
                Ints(out, i.vals);
                out += ',';
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Clear:
                Append(out, "[\"x_clear\",", i.a, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::Replace:
                Append(out, "[\"x_replace\",", i.a, ",", i.b, ",");
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::DestBytes:
                Append(out, "[\"x_dest_bytes\",", i.a, ",");
                Ints(out, vector<int>(i.bytes.begin(), i.bytes.end()));
                out += ',';
                OptOrg(out, i.org);
                out += ']';
                return;
            case GirOp::DestPublish:
                Append(out, "[\"x_dest_publish\",", i.a, ",");
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
            case GirOp::Unreachable: out += "[\"t_unreachable\"]"; return;
            default: return;
        }
    }
};

}  // namespace goose
