// Goose compiler — placement and lowering from GIR-H to GIR-L.
//
// Placement (what lives where):
//
//   * A scalar slot (integer or boolean) is a scalar member of the frame; a
//     fixed array slot is a block of bytes in the frame.
//   * A grow-only slot is a header {base, len} in the frame plus its elements
//     on a data stack of its own, numbered within the function from a hidden
//     base argument (stack `sp + k` for the function's k-th resizable).
//   * A reference to a resizable is two values, the header's address and the
//     stack; any other reference is an address. A slice, and a sampled view,
//     are a data address and a length. A slot that holds a reference or a
//     slice is one member per value.
//   * A function's first parameter is the base of its data stacks. A result
//     that is an array or more than one value is written through an address
//     the caller passes after it, into a temporary of the caller's frame.
//   * A callee's stacks start above all of the caller's, so the program's
//     count is a constant, except through a call cycle: a function in a cycle
//     that owns a resizable is `recursive-resizable`.
//
// `scope.enter` records each resizable's stack top of that scope and every
// exit of the scope restores it. Every check the high stage performs
// implicitly (indexing, slicing) is a compare and a branch to a block that
// aborts. No view, scope, snapshot or checked index remains.
#pragma once

namespace goose {

struct GirLowerUnsupported {
    string feature;
    string where;   // The function.
    int org = -1;   // An origin of the high module, or -1.
};

// The runtime entry points a low module may call; the order is the number an
// RtCall instruction carries.
enum class GirRt : int { OutInt, OutUint, OutBool, OutText, OutNl, Count };

inline const char *GirRtName(int rt) {
    static const char *names[] = { "out_int", "out_uint", "out_bool", "out_text", "out_nl" };
    return names[rt];
}

class GirToLow {
public:
    explicit GirToLow(const GirModule &high) : h(high) {}

    GirModule Lower() {
        l.low = true;
        l.files = h.files;
        l.diagfiles = h.diagfiles;
        l.filemodules = h.filemodules;
        l.origins = h.origins;
        l.entry = h.entry;
        // Signatures first: a call needs its callee's before its body exists.
        for (auto &f : h.funcs) lsigs.push_back(Signature(f));
        for (auto &g : h.globals) l.lowglobals.push_back(PlaceGlobal(g));
        for (auto &f : h.funcs) l.funcs.push_back(LowerFunc(f, -1));
        for (size_t g = 0; g < h.globals.size(); g++) {
            l.initfuncs.push_back((int)l.funcs.size());
            l.funcs.push_back(LowerFunc(h.globals[g].init, (int)g));
        }
        StackTotals();
        return std::move(l);
    }

private:
    const GirModule &h;
    GirModule l;

    // The low signature of each high function: parameter and result types.
    struct Sig {
        vector<GirTypeId> params, results;
        bool out = false;       // The result goes through an address.
        int64_t outsize = 0;
    };
    vector<Sig> lsigs;
    vector<int> gstack;         // The data stack of each resizable global, or -1.

    GirTypeId I64() { return l.IntType(CoreIntTy::I64); }
    GirTypeId U64() { return l.IntType(CoreIntTy::U64); }
    GirTypeId Ptr() { return l.PtrType(); }

    // ---------------------------------------------------------------------
    // Types.

    const CoreType &HT(GirTypeId t) const { return h.Type(t); }

    // The values a high type is made of in the low stage.
    vector<GirTypeId> Words(GirTypeId t) {
        auto &c = HT(t);
        switch (c.kind) {
            case CoreType::Int: return { l.IntType(c.ity) };
            case CoreType::Bool: return { l.BoolType() };
            case CoreType::Arr: return { Ptr() };
            case CoreType::Ref: {
                auto k = HT(c.elem).kind;
                if (k == CoreType::Grow) return { Ptr(), Ptr() };
                if (k == CoreType::Ref || k == CoreType::Slice) return {};   // A slot of one.
                return { Ptr() };
            }
            case CoreType::Slice: case CoreType::View: return { Ptr(), I64() };
            default: return {};
        }
    }

    int64_t Size(GirTypeId t) {
        auto &c = HT(t);
        switch (c.kind) {
            case CoreType::Int: return CoreIntBits(c.ity) / 8;
            case CoreType::Bool: return 1;
            case CoreType::Arr: return c.count * Size(c.elem);
            default: return 8;
        }
    }

    Sig Signature(const GirFunc &f) {
        Sig s;
        s.params.push_back(I64());   // The base of the data stacks.
        if (f.results.size() == 1) {
            auto w = Words(f.results[0]);
            auto arr = HT(f.results[0]).kind == CoreType::Arr;
            if (arr || w.size() > 1) {
                s.out = true;
                s.outsize = arr ? Size(f.results[0]) : 8 * (int64_t)w.size();
                s.params.push_back(Ptr());
            } else if (w.size() == 1) s.results = w;
        }
        for (auto p : f.params)
            for (auto t : Words(p)) s.params.push_back(t);
        return s;
    }

    GirLowGlobal PlaceGlobal(const GirGlobal &g) {
        GirLowGlobal out;
        out.name = g.name;
        out.module = g.module;
        auto k = HT(g.ty).kind;
        out.ty = -1;
        if (k == CoreType::Arr) {
            out.kind = GirMember::Bytes;
            out.size = Size(g.ty);
            gstack.push_back(-1);
        } else if (k == CoreType::Grow) {
            out.kind = GirMember::Header;
            gstack.push_back(l.globalstacks++);
        } else {
            out.kind = GirMember::Scalar;
            out.ty = Words(g.ty)[0];
            gstack.push_back(-1);
        }
        return out;
    }

    // ---------------------------------------------------------------------
    // One function.

    struct Shape {
        vector<int> w;              // The low values.
        int slot = -1;              // A reference to a slot that holds a reference or slice.
        bool lit = false;           // A grow-only array literal, not yet in storage.
        vector<int> elems;          // Its high element values.
    };

    struct Place {
        enum Kind { Scalar, Bytes, Header, Words } kind = Scalar;
        vector<int> members;
        int stack = -1;
    };

    const GirFunc *hf = nullptr;
    GirFunc lf;
    vector<GirTypeId> hvt;          // Type of each high value.
    vector<Shape> shape;
    vector<Place> places;
    vector<int> bmap;               // High block -> its low block.
    vector<GirTypeId> lvals;
    int cur = -1;
    int spval = 0, outval = -1;
    int initglobal = -1;
    const Sig *sig = nullptr;
    // Per scope, the stack tops recorded on entry, by header.
    map<int, vector<int>> marks;
    vector<vector<int>> scopeheaders;   // Per scope, its header slots' places.

    int NewValue(GirTypeId t) {
        lvals.push_back(t);
        return (int)lvals.size() - 1;
    }

    int NewBlockL(const vector<GirTypeId> &params, vector<int> *ids = nullptr) {
        GirBlock b;
        for (auto t : params) {
            auto v = NewValue(t);
            b.params.push_back({ v, t });
            if (ids) ids->push_back(v);
        }
        lf.blocks.push_back(std::move(b));
        return (int)lf.blocks.size() - 1;
    }

    int Emit(GirInst i, GirTypeId ty) {
        if (cur < 0) return 0;
        i.res = NewValue(ty);
        lf.blocks[cur].insts.push_back(std::move(i));
        return lf.blocks[cur].insts.back().res;
    }

    void EmitE(GirInst i) {
        if (cur >= 0) lf.blocks[cur].insts.push_back(std::move(i));
    }

    void Term(GirInst i) {
        if (cur < 0) return;
        lf.blocks[cur].insts.push_back(std::move(i));
        cur = -1;
    }

    int ConstI(GirTypeId ty, int64_t v) {
        GirInst i;
        i.op = GirOp::Int;
        i.ty = ty;
        i.text = to_string(v);
        return Emit(std::move(i), ty);
    }

    int ConstBool(bool b) {
        GirInst i;
        i.op = GirOp::Bool;
        i.flag = b;
        return Emit(std::move(i), l.BoolType());
    }

    int Conv(int v, GirTypeId from, GirTypeId to, CoreConvKind k = CoreConvKind::AsUnchecked,
             int org = -1) {
        if (from == to) return v;
        GirInst i;
        i.op = GirOp::Conv;
        i.conv = k;
        i.ty = from;
        i.ty2 = to;
        i.a = v;
        i.org = org;
        return Emit(std::move(i), to);
    }

    int BinW(CoreBinOp op, GirTypeId ty, int a, int b, bool checked = false, int org = -1) {
        GirInst i;
        i.op = GirOp::Bin;
        i.bin = op;
        i.ty = ty;
        i.a = a;
        i.b = b;
        i.flag = checked;
        i.org = org;
        return Emit(std::move(i), ty);
    }

    int CmpI(CoreCmpOp op, GirTypeId ty, int a, int b) {
        GirInst i;
        i.op = GirOp::Cmp;
        i.cmp = op;
        i.ty = ty;
        i.a = a;
        i.b = b;
        return Emit(std::move(i), l.BoolType());
    }

    int PtrAt(int base, int idx, int64_t esz) {
        GirInst i;
        i.op = GirOp::PtrOffset;
        i.a = base;
        i.b = idx;
        i.idx = (int)esz;
        return Emit(std::move(i), Ptr());
    }

    // The address `k` words past `base`.
    int WordAt(int base, int k) { return PtrAt(base, ConstI(I64(), k), 8); }

    int PLoadV(GirTypeId ty, int p) {
        GirInst i;
        i.op = GirOp::PLoad;
        i.ty = ty;
        i.a = p;
        return Emit(std::move(i), ty);
    }

    void PStoreV(GirTypeId ty, int p, int v) {
        GirInst i;
        i.op = GirOp::PStore;
        i.ty = ty;
        i.a = p;
        i.b = v;
        EmitE(std::move(i));
    }

    void Copy(int dst, int src, int64_t n, bool move = false) {
        GirInst i;
        i.op = move ? GirOp::BytesMove : GirOp::BytesCopy;
        i.a = dst;
        i.b = src;
        i.vals = { ConstI(I64(), n) };
        EmitE(std::move(i));
    }

    int Simple(GirOp op, GirTypeId ty, int a = -1, int b = -1, int idx = -1) {
        GirInst i;
        i.op = op;
        i.a = a;
        i.b = b;
        i.idx = idx;
        return Emit(std::move(i), ty);
    }

    void SimpleE(GirOp op, int a = -1, int b = -1, int idx = -1) {
        GirInst i;
        i.op = op;
        i.a = a;
        i.b = b;
        i.idx = idx;
        EmitE(std::move(i));
    }

    int Member(GirMember m) {
        lf.members.push_back(std::move(m));
        return (int)lf.members.size() - 1;
    }

    int FrameTemp(int64_t size) {
        GirMember m;
        m.kind = GirMember::Bytes;
        m.size = size;
        m.scope = 0;
        m.name = "tmp";
        return Member(std::move(m));
    }

    int StackOf(int k) { return Simple(GirOp::StackAt, Ptr(), spval, -1, k); }

    // A low abort block: the checks branch to one of these.
    int AbortBlock(GirAbortKind kind, vector<int> args, int org, string text = {}) {
        auto saved = cur;
        auto b = NewBlockL({});
        cur = b;
        GirInst i;
        i.op = GirOp::Abort;
        i.abort = kind;
        i.vals = std::move(args);
        i.org = org;
        i.text = std::move(text);
        Term(std::move(i));
        cur = saved;
        return b;
    }

    // Branch on `c` to a new block that carries on, or to `fail`.
    void CheckThen(int c, int fail) {
        auto ok = NewBlockL({});
        GirInst i;
        i.op = GirOp::CondBr;
        i.a = c;
        i.idx = ok;
        i.idx2 = fail;
        Term(std::move(i));
        cur = ok;
    }

    // ---------------------------------------------------------------------

    vector<int> Words_(int hv) { return shape[hv].w; }

    int W0(int hv) { return shape[hv].w.empty() ? 0 : shape[hv].w[0]; }

    bool IsGrowRef(GirTypeId t) {
        auto &c = HT(t);
        return c.kind == CoreType::Ref && HT(c.elem).kind == CoreType::Grow;
    }

    // Places of the slots.
    void PlaceSlots() {
        places.assign(hf->slots.size(), {});
        scopeheaders.assign(hf->scopes.size(), {});
        int stacks = 0;
        for (size_t s = 0; s < hf->slots.size(); s++) {
            auto &sl = hf->slots[s];
            auto &c = HT(sl.ty);
            auto &p = places[s];
            auto name = cat("s", s);
            if (c.kind == CoreType::Arr) {
                p.kind = Place::Bytes;
                GirMember m;
                m.kind = GirMember::Bytes;
                m.size = Size(sl.ty);
                m.scope = sl.scope;
                m.name = name;
                p.members = { Member(std::move(m)) };
            } else if (c.kind == CoreType::Grow) {
                p.kind = Place::Header;
                p.stack = stacks++;
                GirMember m;
                m.kind = GirMember::Header;
                m.scope = sl.scope;
                m.stack = p.stack;
                m.name = name;
                p.members = { Member(std::move(m)) };
                scopeheaders[sl.scope].push_back((int)s);
            } else if (c.kind == CoreType::Int || c.kind == CoreType::Bool) {
                p.kind = Place::Scalar;
                GirMember m;
                m.kind = GirMember::Scalar;
                m.ty = Words(sl.ty)[0];
                m.scope = sl.scope;
                m.name = name;
                p.members = { Member(std::move(m)) };
            } else {
                p.kind = Place::Words;
                for (auto t : Words(sl.ty)) {
                    GirMember m;
                    m.kind = GirMember::Scalar;
                    m.ty = t;
                    m.scope = sl.scope;
                    m.name = name;
                    p.members.push_back(Member(std::move(m)));
                }
            }
        }
        lf.stacks = stacks;
    }

    GirFunc LowerFunc(const GirFunc &f, int global) {
        hf = &f;
        initglobal = global;
        lf = GirFunc {};
        lf.name = f.name;
        lf.org = f.org;
        lf.key = f.key;
        lf.module = f.module;
        lf.summary.unknown = true;   // Effects are a property of the high stage.
        lvals.clear();
        marks.clear();
        shape.clear();
        // Value types of the high function.
        ComputeTypes();
        PlaceSlots();
        // Signature.
        Sig initsig;
        if (global >= 0) initsig.params = { I64() };
        sig = global >= 0 ? &initsig : &lsigs[FuncIndex(f)];
        lf.params = sig->params;
        lf.results = sig->results;
        // Blocks, parameters first.
        bmap.assign(f.blocks.size(), -1);
        shape.assign(hvt.size(), {});
        for (size_t b = 0; b < f.blocks.size(); b++) {
            vector<GirTypeId> ps;
            if (b == 0) ps = lf.params;
            else for (auto &p : f.blocks[b].params) for (auto t : Words(p.second)) ps.push_back(t);
            vector<int> ids;
            bmap[b] = NewBlockL(ps, &ids);
            if (b == 0) {
                spval = ids[0];
                size_t k = 1;
                outval = -1;
                if (global < 0 && sig->out) outval = ids[k++];
                for (auto &p : f.blocks[0].params) {
                    for (auto t : Words(p.second)) { (void)t; shape[p.first].w.push_back(ids[k++]); }
                }
            } else {
                size_t k = 0;
                for (auto &p : f.blocks[b].params)
                    for (auto t : Words(p.second)) { (void)t; shape[p.first].w.push_back(ids[k++]); }
            }
        }
        // Blocks in reverse postorder, so every definition comes before its uses.
        vector<int> order, state(f.blocks.size(), 0);
        function<void(int)> dfs = [&](int b) {
            state[b] = 1;
            auto &t = f.blocks[b].insts.back();
            vector<int> succ;
            if (t.op == GirOp::Br) succ = { t.idx };
            else if (t.op == GirOp::CondBr) succ = { t.idx, t.idx2 };
            for (auto s : succ) if (!state[s]) dfs(s);
            order.push_back(b);
        };
        dfs(0);
        reverse(order.begin(), order.end());
        for (auto b : order) {
            cur = bmap[b];
            for (auto &i : f.blocks[b].insts) Lower(i);
        }
        lf.slots.clear();
        // The scope tree is not kept: the low stage has no scopes, but the
        // frame members keep the scope that bounds their life, as a tree.
        lf.scopes = f.scopes;
        lf.blocks.shrink_to_fit();
        return std::move(lf);
    }

    int FuncIndex(const GirFunc &f) {
        return (int)(&f - h.funcs.data());
    }

    void ComputeTypes() {
        auto &f = *hf;
        int n = 0;
        for (auto &b : f.blocks) {
            n += (int)b.params.size();
            for (auto &i : b.insts) n += GirDefinesValue(i);
        }
        hvt.assign(n, -1);
        for (auto &b : f.blocks) for (auto &p : b.params) hvt[p.first] = p.second;
        vector<pair<vector<GirTypeId>, vector<GirTypeId>>> hsigs;
        for (auto &g : h.funcs) hsigs.push_back({ g.params, g.results });
        auto &mm = const_cast<GirModule &>(h);   // Typing may intern view types.
        for (auto changed = true; changed;) {
            changed = false;
            for (auto &b : f.blocks)
                for (auto &i : b.insts) {
                    if (!GirDefinesValue(i) || hvt[i.res] >= 0) continue;
                    GirTyEnv env { mm, f.slots, hsigs, hvt };
                    auto r = GirTyper(env).Of(i);
                    if (r.ok()) { hvt[i.res] = r.ty; changed = true; }
                }
        }
    }

    // ---------------------------------------------------------------------
    // Instructions.

    void Define(const GirInst &i, vector<int> words) { shape[i.res].w = std::move(words); }

    void Lower(const GirInst &i) {
        switch (i.op) {
            case GirOp::Int: {
                auto t = l.IntType(HT(i.ty).ity);
                GirInst c;
                c.op = GirOp::Int;
                c.ty = t;
                c.text = i.text;
                Define(i, { Emit(std::move(c), t) });
                return;
            }
            case GirOp::Bool: Define(i, { ConstBool(i.flag) }); return;
            case GirOp::Unit: Define(i, {}); return;
            case GirOp::Bin: {
                auto t = l.IntType(HT(i.ty).ity);
                auto checked = i.bin == CoreBinOp::Add || i.bin == CoreBinOp::Sub || i.bin == CoreBinOp::Mul ||
                               i.bin == CoreBinOp::Div || i.bin == CoreBinOp::Mod;
                Define(i, { BinW(i.bin, t, W0(i.a), W0(i.b), checked, i.org) });
                return;
            }
            case GirOp::Un: {
                auto t = l.IntType(HT(i.ty).ity);
                GirInst u;
                u.op = GirOp::Un;
                u.un = i.un;
                u.ty = t;
                u.a = W0(i.a);
                u.flag = i.un == CoreUnOp::Neg;
                u.org = i.org;
                Define(i, { Emit(std::move(u), t) });
                return;
            }
            case GirOp::Cmp: Define(i, { CmpI(i.cmp, l.IntType(HT(i.ty).ity), W0(i.a), W0(i.b)) }); return;
            case GirOp::BoolCmp: Define(i, { CmpI(i.cmp, l.BoolType(), W0(i.a), W0(i.b)) }); return;
            case GirOp::Not: {
                GirInst n;
                n.op = GirOp::Not;
                n.a = W0(i.a);
                Define(i, { Emit(std::move(n), l.BoolType()) });
                return;
            }
            case GirOp::Conv: {
                auto src = l.IntType(HT(i.ty).ity), dst = l.IntType(HT(i.ty2).ity);
                GirInst c;
                c.op = GirOp::Conv;
                c.conv = i.conv;
                c.ty = src;
                c.ty2 = dst;
                c.a = W0(i.a);
                c.org = i.org;
                Define(i, { Emit(std::move(c), dst) });
                return;
            }
            case GirOp::Next: {
                auto t = l.IntType(HT(i.ty).ity);
                Define(i, { BinW(CoreBinOp::Add, t, W0(i.a), ConstI(t, 1)) });
                return;
            }
            case GirOp::Slot: return LowerSlot(i);
            case GirOp::Global: return LowerGlobalAddr(i);
            case GirOp::Elem: {
                auto esz = Size(HT(hvt[i.a]).elem);
                auto idx = ToI64(i.b);
                Define(i, { PtrAt(shape[i.a].w[0], idx, esz) });
                return;
            }
            case GirOp::Freeze: shape[i.res] = shape[i.a]; return;
            case GirOp::Load: return LowerLoad(i);
            case GirOp::Snap: return LowerSnap(i);
            case GirOp::SliceView: shape[i.res].w = shape[i.a].w; return;
            case GirOp::ViewLen: Define(i, { shape[i.a].w[1] }); return;
            case GirOp::ViewSlice: return LowerViewSlice(i);
            case GirOp::ArrayLen: {
                auto &pt = HT(HT(hvt[i.a]).elem);
                if (pt.kind == CoreType::Arr) Define(i, { ConstI(I64(), pt.count) });
                else Define(i, { Simple(GirOp::HdrLen, I64(), shape[i.a].w[0]) });
                return;
            }
            case GirOp::Index: return LowerIndex(i);
            case GirOp::Push: return LowerPush(i);
            case GirOp::Call: return LowerCall(i);
            case GirOp::Arr: return LowerArr(i);
            case GirOp::Fill: return LowerFill(i);
            case GirOp::Init: return LowerInit(i);
            case GirOp::Store: return LowerStore(i);
            case GirOp::Append: return LowerAppend(i);
            case GirOp::Enter: return LowerEnter(i);
            case GirOp::Leave: return LowerLeave(i);
            case GirOp::Print: return LowerPrint(i);
            case GirOp::Br: {
                GirInst b;
                b.op = GirOp::Br;
                b.idx = bmap[i.idx];
                for (auto a : i.vals) for (auto w : shape[a].w) b.vals.push_back(w);
                Term(std::move(b));
                return;
            }
            case GirOp::CondBr: {
                GirInst b;
                b.op = GirOp::CondBr;
                b.a = W0(i.a);
                b.idx = bmap[i.idx];
                b.idx2 = bmap[i.idx2];
                for (auto a : i.vals) for (auto w : shape[a].w) b.vals.push_back(w);
                for (auto a : i.vals2) for (auto w : shape[a].w) b.vals2.push_back(w);
                Term(std::move(b));
                return;
            }
            case GirOp::Ret: return LowerRet(i);
            case GirOp::Abort: {
                GirInst a;
                a.op = GirOp::Abort;
                a.abort = i.abort;
                a.org = i.org;
                a.text = i.text;
                Term(std::move(a));
                return;
            }
            case GirOp::Exit: {
                GirInst e;
                e.op = GirOp::Exit;
                e.a = Conv(W0(i.a), l.IntType(HT(hvt[i.a]).ity), I64());
                e.org = i.org;
                Term(std::move(e));
                return;
            }
            case GirOp::Unreachable: {
                GirInst end;
                end.op = GirOp::Unreachable;
                Term(std::move(end));
                return;
            }
            default: return;
        }
    }

    int ToI64(int hv) {
        auto &c = HT(hvt[hv]);
        return Conv(shape[hv].w[0], l.IntType(c.ity), I64());
    }

    void LowerSlot(const GirInst &i) {
        auto &p = places[i.idx];
        switch (p.kind) {
            case Place::Words: shape[i.res].slot = i.idx; return;
            case Place::Header: {
                auto hdr = Simple(GirOp::FrameAddr, Ptr(), -1, -1, p.members[0]);
                Define(i, { hdr, StackOf(p.stack) });
                return;
            }
            default: Define(i, { Simple(GirOp::FrameAddr, Ptr(), -1, -1, p.members[0]) }); return;
        }
    }

    void LowerGlobalAddr(const GirInst &i) {
        auto &g = l.lowglobals[i.idx];
        auto addr = Simple(GirOp::GlobalAddr, Ptr(), -1, -1, i.idx);
        if (g.kind == GirMember::Header) Define(i, { addr, Simple(GirOp::GlobalStack, Ptr(), -1, -1, i.idx) });
        else Define(i, { addr });
    }

    void LowerLoad(const GirInst &i) {
        auto &rs = shape[i.a];
        auto t = hvt[i.res];
        if (rs.slot >= 0) {
            vector<int> ws;
            for (auto m : places[rs.slot].members) ws.push_back(Simple(GirOp::LocalGet, lf.members[m].ty, -1, -1, m));
            Define(i, std::move(ws));
            return;
        }
        auto &c = HT(t);
        if (c.kind == CoreType::Arr) {
            auto tmp = FrameTemp(Size(t));
            auto dst = Simple(GirOp::FrameAddr, Ptr(), -1, -1, tmp);
            Copy(dst, rs.w[0], Size(t));
            Define(i, { dst });
            return;
        }
        auto lt = Words(t)[0];
        Define(i, { PLoadV(lt, rs.w[0]) });
    }

    void LowerSnap(const GirInst &i) {
        auto &pt = HT(HT(hvt[i.a]).elem);
        auto r = shape[i.a].w[0];
        if (pt.kind == CoreType::Arr) Define(i, { r, ConstI(I64(), pt.count) });
        else Define(i, { Simple(GirOp::HdrBase, Ptr(), r), Simple(GirOp::HdrLen, I64(), r) });
    }

    void LowerViewSlice(const GirInst &i) {
        auto esz = Size(HT(hvt[i.res]).elem);
        auto base = shape[i.a].w[0], n = shape[i.a].w[1];
        auto bound = [&](const GirBound &b, int dflt) {
            if (b.kind == GirBound::None) return dflt;
            auto v = ToI64(b.val);
            if (b.kind == GirBound::Val) return v;
            return BinW(CoreBinOp::Sub, I64(), n, v);
        };
        auto lo = bound(i.lo, ConstI(I64(), 0));
        auto hi = bound(i.hi, n);
        auto fail = AbortBlock(GirAbortKind::SliceOob, {}, i.org);
        auto lou = Conv(lo, I64(), U64()), hiu = Conv(hi, I64(), U64()), nu = Conv(n, I64(), U64());
        CheckThen(CmpI(CoreCmpOp::Le, U64(), lou, hiu), fail);
        CheckThen(CmpI(CoreCmpOp::Le, U64(), hiu, nu), fail);
        auto data = PtrAt(base, lo, esz);
        auto len = BinW(CoreBinOp::Sub, I64(), hi, lo);
        Define(i, { data, len });
    }

    void LowerIndex(const GirInst &i) {
        auto esz = Size(HT(hvt[i.res]).elem);
        auto base = shape[i.a].w[0], n = shape[i.a].w[1];
        auto idx = ToI64(i.b);
        auto fail = AbortBlock(GirAbortKind::IndexOob, { idx, n }, i.org);
        CheckThen(CmpI(CoreCmpOp::Lt, U64(), Conv(idx, I64(), U64()), Conv(n, I64(), U64())), fail);
        Define(i, { PtrAt(base, idx, esz) });
    }

    // Stores the value `w` of high type `t` at `p`.
    void StoreAt(GirTypeId t, int p, const vector<int> &w) {
        auto &c = HT(t);
        if (c.kind == CoreType::Arr) Copy(p, w[0], Size(t));
        else PStoreV(Words(t)[0], p, w[0]);
    }

    void LowerPush(const GirInst &i) {
        auto &rs = shape[i.a];
        auto esz = Size(HT(HT(hvt[i.a]).elem).elem);
        auto elemty = HT(HT(hvt[i.a]).elem).elem;
        auto hdr = rs.w[0], stk = rs.w[1];
        auto base = Simple(GirOp::HdrBase, Ptr(), hdr);
        auto len = Simple(GirOp::HdrLen, I64(), hdr);
        auto at = PtrAt(base, len, esz);
        StoreAt(elemty, at, shape[i.b].w);
        SimpleE(GirOp::StackBump, stk, -1, (int)esz);
        SimpleE(GirOp::HdrSetLen, hdr, BinW(CoreBinOp::Add, I64(), len, ConstI(I64(), 1)));
        Define(i, { at });
    }

    void LowerAppend(const GirInst &i) {
        auto &rs = shape[i.a];
        auto elemty = HT(HT(hvt[i.a]).elem).elem;
        auto esz = Size(elemty);
        auto hdr = rs.w[0], stk = rs.w[1];
        auto src = shape[i.b].w[0], n = shape[i.b].w[1];
        auto base = Simple(GirOp::HdrBase, Ptr(), hdr);
        auto len = Simple(GirOp::HdrLen, I64(), hdr);
        auto at = PtrAt(base, len, esz);
        auto bytes = BinW(CoreBinOp::Mul, I64(), n, ConstI(I64(), esz));
        GirInst c;
        c.op = GirOp::BytesMove;
        c.a = at;
        c.b = src;
        c.vals = { bytes };
        EmitE(std::move(c));
        SimpleE(GirOp::StackBump, stk, bytes);
        SimpleE(GirOp::HdrSetLen, hdr, BinW(CoreBinOp::Add, I64(), len, n));
    }

    void LowerArr(const GirInst &i) {
        auto &c = HT(i.ty);
        if (c.kind == CoreType::Grow) {
            shape[i.res].lit = true;
            shape[i.res].elems = i.vals;
            return;
        }
        auto esz = Size(c.elem);
        auto tmp = FrameTemp(Size(i.ty));
        auto dst = Simple(GirOp::FrameAddr, Ptr(), -1, -1, tmp);
        for (size_t k = 0; k < i.vals.size(); k++)
            StoreAt(c.elem, PtrAt(dst, ConstI(I64(), (int64_t)k), esz), shape[i.vals[k]].w);
        Define(i, { dst });
    }

    void LowerFill(const GirInst &i) {
        auto &c = HT(i.ty);
        auto esz = Size(c.elem);
        auto tmp = FrameTemp(Size(i.ty));
        auto dst = Simple(GirOp::FrameAddr, Ptr(), -1, -1, tmp);
        int src;
        auto &w = shape[i.a].w;
        if (HT(c.elem).kind == CoreType::Arr) src = w[0];
        else {
            auto one = FrameTemp(esz);
            src = Simple(GirOp::FrameAddr, Ptr(), -1, -1, one);
            PStoreV(Words(c.elem)[0], src, w[0]);
        }
        GirInst f;
        f.op = GirOp::BytesFill;
        f.a = dst;
        f.b = src;
        f.idx = (int)esz;
        f.vals = { ConstI(I64(), c.count) };
        EmitE(std::move(f));
        Define(i, { dst });
    }

    // Initializes a resizable's header at `hdr`, on `stk`, with a literal.
    void InitGrow(int hdr, int stk, GirTypeId growty, const Shape &lit) {
        auto elemty = HT(growty).elem;
        auto esz = Size(elemty);
        auto base = Simple(GirOp::StackMark, Ptr(), stk);
        SimpleE(GirOp::HdrInit, hdr, base);
        auto n = (int64_t)lit.elems.size();
        for (int64_t k = 0; k < n; k++)
            StoreAt(elemty, PtrAt(base, ConstI(I64(), k), esz), shape[lit.elems[k]].w);
        if (n) {
            SimpleE(GirOp::StackBump, stk, -1, (int)(n * esz));
            SimpleE(GirOp::HdrSetLen, hdr, ConstI(I64(), n));
        }
    }

    void LowerInit(const GirInst &i) {
        auto &p = places[i.idx];
        auto t = hf->slots[i.idx].ty;
        auto &v = shape[i.a];
        switch (p.kind) {
            case Place::Scalar: SimpleE(GirOp::LocalSet, v.w[0], -1, p.members[0]); return;
            case Place::Bytes: {
                auto dst = Simple(GirOp::FrameAddr, Ptr(), -1, -1, p.members[0]);
                Copy(dst, v.w[0], Size(t));
                return;
            }
            case Place::Header: {
                auto hdr = Simple(GirOp::FrameAddr, Ptr(), -1, -1, p.members[0]);
                InitGrow(hdr, StackOf(p.stack), t, v);
                return;
            }
            case Place::Words:
                for (size_t k = 0; k < p.members.size(); k++)
                    SimpleE(GirOp::LocalSet, v.w[k], -1, p.members[k]);
                return;
        }
    }

    void LowerStore(const GirInst &i) {
        auto &rs = shape[i.a];
        auto &v = shape[i.b];
        if (rs.slot >= 0) {
            auto &p = places[rs.slot];
            for (size_t k = 0; k < p.members.size(); k++)
                SimpleE(GirOp::LocalSet, v.w[k], -1, p.members[k]);
            return;
        }
        StoreAt(hvt[i.b], rs.w[0], v.w);
    }

    void LowerEnter(const GirInst &i) {
        vector<int> ms;
        for (auto s : scopeheaders[i.idx]) ms.push_back(Simple(GirOp::StackMark, Ptr(), StackOf(places[s].stack)));
        marks[i.idx] = std::move(ms);
    }

    void LowerLeave(const GirInst &i) {
        auto &hs = scopeheaders[i.idx];
        auto it = marks.find(i.idx);
        for (size_t k = hs.size(); k > 0; k--)
            SimpleE(GirOp::StackRelease, StackOf(places[hs[k - 1]].stack), it->second[k - 1]);
    }

    void RtCall(GirRt rt, int arg = -1, string text = {}) {
        GirInst c;
        c.op = GirOp::RtCall;
        c.idx = (int)rt;
        c.a = arg;
        c.text = std::move(text);
        EmitE(std::move(c));
    }

    void LowerPrint(const GirInst &i) {
        for (auto &p : i.parts) {
            if (p.text) { RtCall(GirRt::OutText, -1, p.str); continue; }
            auto &c = HT(hvt[p.val]);
            if (c.kind == CoreType::Bool) RtCall(GirRt::OutBool, shape[p.val].w[0]);
            else RtCall(CoreIsUnsigned(c.ity) ? GirRt::OutUint : GirRt::OutInt, shape[p.val].w[0]);
        }
        RtCall(GirRt::OutNl);
    }

    void LowerCall(const GirInst &i) {
        auto &g = h.funcs[i.idx];
        auto &s = lsigs[i.idx];
        GirInst c;
        c.op = GirOp::Call;
        c.idx = i.idx;
        c.org = i.org;
        c.vals.push_back(lf.stacks ? BinW(CoreBinOp::Add, I64(), spval, ConstI(I64(), lf.stacks)) : spval);
        int tmp = -1, tmpaddr = -1;
        if (s.out) {
            tmp = FrameTemp(s.outsize);
            tmpaddr = Simple(GirOp::FrameAddr, Ptr(), -1, -1, tmp);
            c.vals.push_back(tmpaddr);
        }
        for (auto a : i.vals) for (auto w : shape[a].w) c.vals.push_back(w);
        if (s.results.empty()) {
            EmitE(std::move(c));
        } else {
            Define(i, { Emit(std::move(c), s.results[0]) });
            return;
        }
        if (!s.out) { Define(i, {}); return; }
        auto rt = g.results[0];
        if (HT(rt).kind == CoreType::Arr) { Define(i, { tmpaddr }); return; }
        vector<int> ws;
        auto words = Words(rt);
        for (size_t k = 0; k < words.size(); k++) ws.push_back(PLoadV(words[k], WordAt(tmpaddr, (int)k)));
        Define(i, std::move(ws));
    }

    void LowerRet(const GirInst &i) {
        if (initglobal >= 0) return LowerGlobalRet(i);
        if (!i.vals.empty()) {
            auto &v = shape[i.vals[0]];
            if (sig->out) {
                auto rt = hf->results[0];
                if (HT(rt).kind == CoreType::Arr) Copy(outval, v.w[0], Size(rt));
                else {
                    auto words = Words(rt);
                    for (size_t k = 0; k < words.size(); k++) PStoreV(words[k], WordAt(outval, (int)k), v.w[k]);
                }
            }
        }
        GirInst r;
        r.op = GirOp::Ret;
        if (!i.vals.empty() && !sig->out && !shape[i.vals[0]].w.empty()) r.vals = { shape[i.vals[0]].w[0] };
        Term(std::move(r));
    }

    // A global's initializer writes the value into the global's storage.
    void LowerGlobalRet(const GirInst &i) {
        auto &g = h.globals[initglobal];
        auto &lg = l.lowglobals[initglobal];
        auto &v = shape[i.vals[0]];
        auto addr = Simple(GirOp::GlobalAddr, Ptr(), -1, -1, initglobal);
        if (lg.kind == GirMember::Header) {
            auto stk = Simple(GirOp::GlobalStack, Ptr(), -1, -1, initglobal);
            InitGrow(addr, stk, g.ty, v);
        } else {
            StoreAt(g.ty, addr, v.w);
        }
        GirInst r;
        r.op = GirOp::Ret;
        Term(std::move(r));
    }

    // ---------------------------------------------------------------------
    // How many data stacks the program starts with.

    void StackTotals() {
        auto n = l.funcs.size();
        vector<vector<int>> callees(n);
        for (size_t f = 0; f < n; f++)
            for (auto &b : l.funcs[f].blocks)
                for (auto &i : b.insts)
                    if (i.op == GirOp::Call) callees[f].push_back(i.idx);
        // Tarjan's components, callees' before callers'.
        vector<int> index(n, -1), low(n, 0), stack, need(n, 0);
        vector<char> onstack(n, 0);
        int next = 0;
        function<void(int)> visit = [&](int v) {
            index[v] = low[v] = next++;
            stack.push_back(v);
            onstack[v] = 1;
            for (auto w : callees[v]) {
                if (index[w] < 0) {
                    visit(w);
                    low[v] = min(low[v], low[w]);
                } else if (onstack[w]) low[v] = min(low[v], index[w]);
            }
            if (low[v] != index[v]) return;
            vector<int> scc;
            for (;;) {
                auto w = stack.back();
                stack.pop_back();
                onstack[w] = 0;
                scc.push_back(w);
                if (w == v) break;
            }
            auto cycle = scc.size() > 1 ||
                         find(callees[v].begin(), callees[v].end(), v) != callees[v].end();
            int total = 0;
            for (auto m : scc) {
                if (cycle && l.funcs[m].stacks > 0)
                    throw GirLowerUnsupported { "recursive-resizable", l.funcs[m].name, l.funcs[m].org };
                int calls = 0;
                for (auto c : callees[m])
                    if (find(scc.begin(), scc.end(), c) == scc.end()) calls = max(calls, need[c]);
                total = max(total, l.funcs[m].stacks + calls);
            }
            for (auto m : scc) need[m] = total;
        };
        for (size_t f = 0; f < n; f++) if (index[f] < 0) visit((int)f);
        l.mainstacks = need[l.entry];
        for (auto g : l.initfuncs) l.mainstacks = max(l.mainstacks, need[g]);
    }
};

}  // namespace goose
