// Goose compiler — placement and lowering from GIR-H to GIR-L.
//
// Placement (what lives where):
//
//   * A scalar slot (integer or boolean) is a scalar member of the frame; a
//     fixed array slot is a block of bytes in the frame.
//   * A grow/growshrink slot is a header {base, len} in the frame plus its
//     elements on a data stack of its own, numbered within the function from
//     a hidden base argument (stack `sp + k` for the function's k-th owner).
//   * A reference to a resizable owner is two values, the header's address and
//     the stack; a limited owner is an address of its inline length and slots.
//     Any other reference is an address. A slice, and a sampled view, are a
//     data address and a length. A slot that holds a reference or slice is one
//     member per value.
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
        l.profile = h.profile;
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
            case CoreType::Struct: return { Ptr() };
            case CoreType::Ref: {
                auto k = HT(c.elem).kind;
                if (IsResizableKind(k)) return { Ptr(), Ptr() };
                if (k == CoreType::Slice) return { Ptr() };  // Address of the two-word slice slot.
                if (k == CoreType::Ref) return {};           // A slot of one.
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
            case CoreType::Limited: {
                auto prefix = IntBits(LimitedLengthStorage(c.count)) / 8;
                auto element = Size(c.elem);
                if (element <= 0 || c.count > (INT64_MAX - prefix) / element)
                    throw GirLowerUnsupported { "limited-capacity", hf ? hf->name : "global",
                                                hf ? hf->org : -1 };
                return prefix + c.count * element;
            }
            case CoreType::Slice: return 16;
            case CoreType::Struct: return h.structs.at(c.structid).size;
            default: return 8;
        }
    }

    int64_t LowScalarSize(GirTypeId t) const {
        auto &c = l.Type(t);
        if (c.kind == CoreType::Int) return CoreIntBits(c.ity) / 8;
        if (c.kind == CoreType::Bool) return 1;
        throw CompileError { "internal compiler error: byte access requires a scalar type" };
    }

    Sig Signature(const GirFunc &f) {
        Sig s;
        s.params.push_back(I64());   // The base of the data stacks.
        if (f.results.size() == 1) {
            auto w = Words(f.results[0]);
            auto kind = HT(f.results[0]).kind;
            auto arr = kind == CoreType::Arr;
            auto aggregate = arr || kind == CoreType::Struct;
            if (aggregate || w.size() > 1) {
                s.out = true;
                s.outsize = aggregate ? Size(f.results[0]) : 8 * (int64_t)w.size();
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
        if (k == CoreType::Arr || k == CoreType::Struct || k == CoreType::Limited) {
            out.kind = GirMember::Bytes;
            out.size = Size(g.ty);
            gstack.push_back(-1);
        } else if (IsResizableKind(k)) {
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
        bool unaligned = false;     // An address inside a packed struct may lack scalar alignment.
        bool lit = false;           // A transient owner literal run, static or joined.
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
    vector<int> blockparammembers;  // Owned byte storage for aggregate block parameters.
    vector<int> blockparamrunmembers; // Byte storage for transient owner-run parameters.
    vector<int> blockparamrunlens;  // Length members for transient owner-run parameters.
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

    bool IsAggregate(GirTypeId ty) const {
        auto kind = HT(ty).kind;
        return kind == CoreType::Arr || kind == CoreType::Struct;
    }

    bool IsOwnerRun(GirTypeId ty) const { return GirOwnerKind(HT(ty).kind); }

    // Literal-run joins need only the largest static alternative for storage.
    int64_t MaxOwnerRunElements(GirTypeId ty) const {
        int64_t count = 0;
        for (auto &block : hf->blocks)
            for (auto &inst : block.insts)
                if (inst.op == GirOp::Arr && inst.ty == ty)
                    count = max(count, (int64_t)inst.vals.size());
        return count;
    }

    int64_t OwnerRunBufferSize(GirTypeId ty) {
        auto element = Size(HT(ty).elem);
        auto count = MaxOwnerRunElements(ty);
        if (element <= 0 || count > INT64_MAX / element)
            throw GirLowerUnsupported { "owner-run", hf ? hf->name : "global", hf ? hf->org : -1 };
        return max<int64_t>(1, count * element);
    }

    int OwnerRunBytes(GirTypeId ty, int length) {
        return BinW(CoreBinOp::Mul, I64(), length,
                    ConstI(I64(), Size(HT(ty).elem)));
    }

    void CopyDynamic(int dst, int src, int bytes) {
        GirInst copy;
        copy.op = GirOp::BytesCopy;
        copy.a = dst;
        copy.b = src;
        copy.vals = { bytes };
        EmitE(std::move(copy));
    }

    bool HasAggregateParams(int block) const {
        for (auto &param : hf->blocks[block].params)
            if (IsAggregate(param.second) || IsOwnerRun(param.second)) return true;
        return false;
    }

    vector<int> BranchValues(int target, const vector<int> &values) {
        struct PendingCopy {
            int scratch;
            int dest;
            int64_t size;
            int length = -1;
            int lengthMember = -1;
            GirTypeId runType = -1;
        };
        vector<int> words;
        vector<PendingCopy> pending;
        auto &params = hf->blocks[target].params;
        for (size_t k = 0; k < params.size(); k++) {
            auto [param, ty] = params[k];
            auto value = values[k];
            if (IsAggregate(ty)) {
                auto scratch = FrameTemp(Size(ty));
                auto scratchAddress = Simple(GirOp::FrameAddr, Ptr(), -1, -1, scratch);
                Copy(scratchAddress, shape[value].w[0], Size(ty));
                pending.push_back({ scratch, blockparammembers[param], Size(ty) });
            } else if (IsOwnerRun(ty)) {
                auto scratch = FrameTemp(OwnerRunBufferSize(ty));
                auto scratchAddress = Simple(GirOp::FrameAddr, Ptr(), -1, -1, scratch);
                int length;
                if (shape[value].w.size() == 2) {
                    length = shape[value].w[1];
                    CopyDynamic(scratchAddress, shape[value].w[0], OwnerRunBytes(ty, length));
                } else if (shape[value].lit) {
                    length = ConstI(I64(), (int64_t)shape[value].elems.size());
                    auto elem = HT(ty).elem;
                    auto elementSize = Size(elem);
                    for (size_t j = 0; j < shape[value].elems.size(); j++)
                        StoreAt(elem, PtrAt(scratchAddress, ConstI(I64(), (int64_t)j), elementSize),
                                shape[shape[value].elems[j]].w);
                } else {
                    throw GirLowerUnsupported { "owner-run", hf->name, hf->org };
                }
                pending.push_back({ scratch, blockparamrunmembers[param], 0, length,
                                    blockparamrunlens[param], ty });
            } else {
                for (auto word : shape[value].w) words.push_back(word);
            }
        }
        // Stage every source first so parallel block-parameter assignments do
        // not overwrite an aggregate that another parameter still needs.
        for (auto &copy : pending) {
            auto src = Simple(GirOp::FrameAddr, Ptr(), -1, -1, copy.scratch);
            auto dst = Simple(GirOp::FrameAddr, Ptr(), -1, -1, copy.dest);
            if (copy.runType >= 0) {
                CopyDynamic(dst, src, OwnerRunBytes(copy.runType, copy.length));
                SimpleE(GirOp::LocalSet, copy.length, -1, copy.lengthMember);
            } else {
                Copy(dst, src, copy.size);
            }
        }
        return words;
    }

    void LowerBranch(int target, const vector<int> &values) {
        GirInst branch;
        branch.op = GirOp::Br;
        branch.idx = bmap[target];
        branch.vals = BranchValues(target, values);
        Term(std::move(branch));
    }

    int LowerBranchEdge(int target, const vector<int> &values) {
        auto edge = NewBlockL({});
        cur = edge;
        LowerBranch(target, values);
        return edge;
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
        return c.kind == CoreType::Ref && IsResizableKind(HT(c.elem).kind);
    }

    bool IsResizableKind(CoreType::Kind kind) const {
        return kind == CoreType::Grow || kind == CoreType::GrowShrink;
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
            if (c.kind == CoreType::Arr || c.kind == CoreType::Struct) {
                p.kind = Place::Bytes;
                GirMember m;
                m.kind = GirMember::Bytes;
                m.size = Size(sl.ty);
                m.scope = sl.scope;
                m.name = name;
                p.members = { Member(std::move(m)) };
            } else if (c.kind == CoreType::Slice) {
                p.kind = Place::Bytes;
                GirMember m;
                m.kind = GirMember::Bytes;
                m.size = Size(sl.ty);
                m.scope = sl.scope;
                m.name = name;
                p.members = { Member(std::move(m)) };
            } else if (IsResizableKind(c.kind)) {
                p.kind = Place::Header;
                p.stack = stacks++;
                GirMember m;
                m.kind = GirMember::Header;
                m.scope = sl.scope;
                m.stack = p.stack;
                m.name = name;
                p.members = { Member(std::move(m)) };
                scopeheaders[sl.scope].push_back((int)s);
            } else if (c.kind == CoreType::Limited) {
                p.kind = Place::Bytes;
                GirMember m;
                m.kind = GirMember::Bytes;
                m.size = Size(sl.ty);
                m.scope = sl.scope;
                m.name = name;
                p.members = { Member(std::move(m)) };
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
        blockparammembers.assign(hvt.size(), -1);
        blockparamrunmembers.assign(hvt.size(), -1);
        blockparamrunlens.assign(hvt.size(), -1);
        shape.assign(hvt.size(), {});
        // A reference to a scalar can arrive from a packed field through a
        // block parameter or a call result. The high type does not retain
        // alignment, so keep shrink-profile scalar references byte-safe at
        // every boundary where that provenance can be erased.
        if (h.profile == CoreProfile::Shrink)
            for (size_t v = 0; v < hvt.size(); v++) {
                auto &t = HT(hvt[v]);
                if (t.kind == CoreType::Ref &&
                    (HT(t.elem).kind == CoreType::Int || HT(t.elem).kind == CoreType::Bool))
                    shape[v].unaligned = true;
            }
        for (auto &block : f.blocks)
            for (auto &param : block.params)
                if (IsAggregate(param.second))
                    blockparammembers[param.first] = FrameTemp(Size(param.second));
                else if (IsOwnerRun(param.second)) {
                    blockparamrunmembers[param.first] = FrameTemp(OwnerRunBufferSize(param.second));
                    GirMember length;
                    length.kind = GirMember::Scalar;
                    length.ty = I64();
                    length.scope = 0;
                    length.name = "owner_run_len";
                    blockparamrunlens[param.first] = Member(std::move(length));
                }
        for (size_t b = 0; b < f.blocks.size(); b++) {
            vector<GirTypeId> ps;
            if (b == 0) ps = lf.params;
            else for (auto &p : f.blocks[b].params)
                if (!IsAggregate(p.second) && !IsOwnerRun(p.second))
                    for (auto t : Words(p.second)) ps.push_back(t);
            vector<int> ids;
            bmap[b] = NewBlockL(ps, &ids);
            if (b == 0) {
                spval = ids[0];
                size_t k = 1;
                outval = -1;
                if (global < 0 && sig->out) outval = ids[k++];
                for (auto &p : f.blocks[0].params) {
                    if (IsOwnerRun(p.second))
                        throw GirLowerUnsupported { "owner-run-parameter", f.name, f.org };
                    for (auto t : Words(p.second)) { (void)t; shape[p.first].w.push_back(ids[k++]); }
                }
            } else {
                size_t k = 0;
                for (auto &p : f.blocks[b].params)
                    if (!IsAggregate(p.second) && !IsOwnerRun(p.second))
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
            if (b == 0 && global < 0) {
                for (auto &p : f.blocks[0].params) {
                    if (!IsAggregate(p.second)) continue;
                    auto copy = blockparammembers[p.first];
                    auto dst = Simple(GirOp::FrameAddr, Ptr(), -1, -1, copy);
                    Copy(dst, shape[p.first].w[0], Size(p.second));
                    shape[p.first].w[0] = dst;
                }
            } else if (b > 0) {
                for (auto &p : f.blocks[b].params) {
                    if (!IsAggregate(p.second)) continue;
                    shape[p.first].w = { Simple(GirOp::FrameAddr, Ptr(), -1, -1,
                                                blockparammembers[p.first]) };
                }
                for (auto &p : f.blocks[b].params) {
                    if (!IsOwnerRun(p.second)) continue;
                    shape[p.first].lit = true;
                    shape[p.first].w = {
                        Simple(GirOp::FrameAddr, Ptr(), -1, -1, blockparamrunmembers[p.first]),
                        Simple(GirOp::LocalGet, I64(), -1, -1, blockparamrunlens[p.first]),
                    };
                }
            }
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
            case GirOp::Field: {
                auto ref = hvt[i.a];
                auto owner = HT(ref).elem;
                auto sid = HT(owner).structid;
                auto offset = h.structs.at(sid).fields.at(i.idx).offset;
                Define(i, { PtrAt(shape[i.a].w[0], ConstI(I64(), offset), 1) });
                shape[i.res].unaligned = true;
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
                else if (pt.kind == CoreType::Limited)
                    Define(i, { LimitedLength(shape[i.a].w[0], HT(hvt[i.a]).elem) });
                else Define(i, { Simple(GirOp::HdrLen, I64(), shape[i.a].w[0]) });
                return;
            }
            case GirOp::Index: return LowerIndex(i);
            case GirOp::Push: return LowerPush(i);
            case GirOp::Pop: return LowerPop(i);
            case GirOp::Call: return LowerCall(i);
            case GirOp::Arr: return LowerArr(i);
            case GirOp::Struct: return LowerStruct(i);
            case GirOp::Fill: return LowerFill(i);
            case GirOp::Init: return LowerInit(i);
            case GirOp::Store: return LowerStore(i);
            case GirOp::Append: return LowerAppend(i);
            case GirOp::PopN: return LowerPopN(i);
            case GirOp::Resize: return LowerResize(i);
            case GirOp::Clear: return LowerClear(i);
            case GirOp::Replace: return LowerReplace(i);
            case GirOp::Enter: return LowerEnter(i);
            case GirOp::Leave: return LowerLeave(i);
            case GirOp::Print: return LowerPrint(i);
            case GirOp::Br: {
                LowerBranch(i.idx, i.vals);
                return;
            }
            case GirOp::CondBr: {
                if (HasAggregateParams(i.idx) || HasAggregateParams(i.idx2)) {
                    auto current = cur;
                    auto thenEdge = LowerBranchEdge(i.idx, i.vals);
                    auto elseEdge = LowerBranchEdge(i.idx2, i.vals2);
                    cur = current;
                    GirInst branch;
                    branch.op = GirOp::CondBr;
                    branch.a = W0(i.a);
                    branch.idx = thenEdge;
                    branch.idx2 = elseEdge;
                    Term(std::move(branch));
                    return;
                }
                GirInst b;
                b.op = GirOp::CondBr;
                b.a = W0(i.a);
                b.idx = bmap[i.idx];
                b.idx2 = bmap[i.idx2];
                b.vals = BranchValues(i.idx, i.vals);
                b.vals2 = BranchValues(i.idx2, i.vals2);
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
        if (c.kind == CoreType::Arr || c.kind == CoreType::Struct) {
            auto tmp = FrameTemp(Size(t));
            auto dst = Simple(GirOp::FrameAddr, Ptr(), -1, -1, tmp);
            Copy(dst, rs.w[0], Size(t));
            Define(i, { dst });
            return;
        }
        if (c.kind == CoreType::Slice) {
            Define(i, { PLoadV(Ptr(), rs.w[0]), PLoadV(I64(), WordAt(rs.w[0], 1)) });
            return;
        }
        auto lt = Words(t)[0];
        if (rs.unaligned) {
            Define(i, { LoadScalarBytes(lt, rs.w[0]) });
            return;
        }
        Define(i, { PLoadV(lt, rs.w[0]) });
    }

    void LowerSnap(const GirInst &i) {
        auto owner = HT(hvt[i.a]).elem;
        auto &pt = HT(owner);
        auto r = shape[i.a].w[0];
        if (pt.kind == CoreType::Arr) Define(i, { r, ConstI(I64(), pt.count) });
        else if (pt.kind == CoreType::Limited)
            Define(i, { LimitedData(r, owner), LimitedLength(r, owner) });
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

    GirTypeId LimitedLengthType(GirTypeId owner) {
        auto storage = LimitedLengthStorage(HT(owner).count);
        CoreIntTy kind;
        switch (storage) {
            case IS_U8: kind = CoreIntTy::U8; break;
            case IS_U16: kind = CoreIntTy::U16; break;
            case IS_U32: kind = CoreIntTy::U32; break;
            case IS_U64: kind = CoreIntTy::U64; break;
            default: throw CompileError { "internal compiler error: limited length is not unsigned" };
        }
        return l.IntType(kind);
    }

    int64_t LimitedPrefix(GirTypeId owner) {
        return IntBits(LimitedLengthStorage(HT(owner).count)) / 8;
    }

    int LimitedData(int address, GirTypeId owner) {
        return PtrAt(address, ConstI(I64(), LimitedPrefix(owner)), 1);
    }

    int LimitedLength(int address, GirTypeId owner) {
        auto ty = LimitedLengthType(owner);
        auto value = LoadScalarBytes(ty, address);
        return Conv(value, ty, I64(), CoreConvKind::Widen);
    }

    void SetLimitedLength(int address, GirTypeId owner, int length) {
        auto ty = LimitedLengthType(owner);
        auto value = Conv(length, I64(), ty, CoreConvKind::AsUnchecked);
        StoreScalarBytes(ty, address, value);
    }

    void InitLimited(int address, GirTypeId owner, const Shape &run) {
        auto elem = HT(owner).elem;
        auto esz = Size(elem);
        auto data = LimitedData(address, owner);
        if (run.w.size() == 2) {
            auto bytes = OwnerRunBytes(owner, run.w[1]);
            CopyDynamic(data, run.w[0], bytes);
            SetLimitedLength(address, owner, run.w[1]);
            return;
        }
        SetLimitedLength(address, owner, ConstI(I64(), (int64_t)run.elems.size()));
        for (size_t i = 0; i < run.elems.size(); i++)
            StoreAt(elem, PtrAt(data, ConstI(I64(), (int64_t)i), esz), shape[run.elems[i]].w);
    }

    // Stores the value `w` of high type `t` at `p`.
    void StoreAt(GirTypeId t, int p, const vector<int> &w) {
        auto &c = HT(t);
        if (c.kind == CoreType::Arr) Copy(p, w[0], Size(t));
        else if (c.kind == CoreType::Slice) {
            PStoreV(Ptr(), p, w[0]);
            PStoreV(I64(), WordAt(p, 1), w[1]);
        }
        else if (c.kind == CoreType::Struct) Copy(p, w[0], Size(t));
        else if (h.profile == CoreProfile::Shrink)
            StoreScalarBytes(Words(t)[0], p, w[0]);
        else PStoreV(Words(t)[0], p, w[0]);
    }

    GirTypeId OwnerType(int reference) const { return HT(hvt[reference]).elem; }

    GirTypeId OwnerElement(GirTypeId owner) const { return HT(owner).elem; }

    int OwnerLength(int reference, GirTypeId owner) {
        auto address = shape[reference].w[0];
        if (HT(owner).kind == CoreType::Limited) return LimitedLength(address, owner);
        return Simple(GirOp::HdrLen, I64(), address);
    }

    int OwnerData(int reference, GirTypeId owner) {
        auto address = shape[reference].w[0];
        if (HT(owner).kind == CoreType::Limited) return LimitedData(address, owner);
        return Simple(GirOp::HdrBase, Ptr(), address);
    }

    void SetOwnerLength(int reference, GirTypeId owner, int length) {
        auto address = shape[reference].w[0];
        if (HT(owner).kind == CoreType::Limited) SetLimitedLength(address, owner, length);
        else SimpleE(GirOp::HdrSetLen, address, length);
    }

    void ReleaseOwnerTo(int reference, int length, int top) {
        auto &words = shape[reference].w;
        SimpleE(GirOp::StackRelease, words[1], top);
        SimpleE(GirOp::HdrSetLen, words[0], length);
    }

    int ScalarValueAddress(GirTypeId type, int value) {
        auto tmp = FrameTemp(Size(type));
        auto address = Simple(GirOp::FrameAddr, Ptr(), -1, -1, tmp);
        StoreScalarBytes(Words(type)[0], address, value);
        return address;
    }

    int LoadScalarBytes(GirTypeId ty, int src) {
        GirMember member;
        member.kind = GirMember::Scalar;
        member.ty = ty;
        member.scope = 0;
        member.name = "field_load";
        auto index = Member(std::move(member));
        auto dst = Simple(GirOp::FrameAddr, Ptr(), -1, -1, index);
        Copy(dst, src, LowScalarSize(ty));
        return Simple(GirOp::LocalGet, ty, -1, -1, index);
    }

    void StoreScalarBytes(GirTypeId ty, int dst, int value) {
        GirMember member;
        member.kind = GirMember::Scalar;
        member.ty = ty;
        member.scope = 0;
        member.name = "field_store";
        auto index = Member(std::move(member));
        SimpleE(GirOp::LocalSet, value, -1, index);
        auto src = Simple(GirOp::FrameAddr, Ptr(), -1, -1, index);
        Copy(dst, src, LowScalarSize(ty));
    }

    void LowerPush(const GirInst &i) {
        auto &rs = shape[i.a];
        auto owner = OwnerType(i.a);
        auto elemty = OwnerElement(owner);
        auto esz = Size(elemty);
        auto address = rs.w[0];
        auto len = OwnerLength(i.a, owner);
        auto limited = HT(owner).kind == CoreType::Limited;
        if (limited) {
            auto fail = AbortBlock(GirAbortKind::Capacity, {}, i.org);
            CheckThen(CmpI(CoreCmpOp::Lt, I64(), len, ConstI(I64(), HT(owner).count)), fail);
        }
        auto base = OwnerData(i.a, owner);
        auto at = PtrAt(base, len, esz);
        StoreAt(elemty, at, shape[i.b].w);
        auto newLen = BinW(CoreBinOp::Add, I64(), len, ConstI(I64(), 1), true, i.org);
        if (limited) SetLimitedLength(address, owner, newLen);
        else {
            SimpleE(GirOp::StackBump, rs.w[1], -1, (int)esz);
            SimpleE(GirOp::HdrSetLen, address, newLen);
        }
        Define(i, { at });
    }

    void LowerAppend(const GirInst &i) {
        auto &rs = shape[i.a];
        auto owner = OwnerType(i.a);
        auto elemty = OwnerElement(owner);
        auto esz = Size(elemty);
        auto src = shape[i.b].w[0], n = shape[i.b].w[1];
        auto address = rs.w[0];
        auto len = OwnerLength(i.a, owner);
        auto limited = HT(owner).kind == CoreType::Limited;
        if (limited) {
            auto room = BinW(CoreBinOp::Sub, I64(), ConstI(I64(), HT(owner).count), len);
            auto nUnsigned = Conv(n, I64(), U64(), CoreConvKind::AsUnchecked);
            auto roomUnsigned = Conv(room, I64(), U64(), CoreConvKind::AsUnchecked);
            auto fail = AbortBlock(GirAbortKind::Capacity, {}, i.org);
            CheckThen(CmpI(CoreCmpOp::Le, U64(), nUnsigned, roomUnsigned), fail);
        }
        auto base = OwnerData(i.a, owner);
        auto at = PtrAt(base, len, esz);
        auto bytes = BinW(CoreBinOp::Mul, I64(), n, ConstI(I64(), esz), true, i.org);
        GirInst c;
        c.op = GirOp::BytesMove;
        c.a = at;
        c.b = src;
        c.vals = { bytes };
        EmitE(std::move(c));
        auto newLen = BinW(CoreBinOp::Add, I64(), len, n, true, i.org);
        if (limited) SetLimitedLength(address, owner, newLen);
        else {
            SimpleE(GirOp::StackBump, rs.w[1], bytes);
            SimpleE(GirOp::HdrSetLen, address, newLen);
        }
    }

    void LowerPop(const GirInst &i) {
        auto owner = OwnerType(i.a);
        auto elem = OwnerElement(owner);
        auto esz = Size(elem);
        auto len = OwnerLength(i.a, owner);
        auto fail = AbortBlock(GirAbortKind::PopEmpty, {}, i.org);
        CheckThen(CmpI(CoreCmpOp::Lt, I64(), ConstI(I64(), 0), len), fail);
        auto newLen = BinW(CoreBinOp::Sub, I64(), len, ConstI(I64(), 1));
        auto base = OwnerData(i.a, owner);
        auto at = PtrAt(base, newLen, esz);
        vector<int> value;
        auto &element = HT(elem);
        if (element.kind == CoreType::Arr || element.kind == CoreType::Struct) {
            auto tmp = FrameTemp(esz);
            auto address = Simple(GirOp::FrameAddr, Ptr(), -1, -1, tmp);
            Copy(address, at, esz);
            value = { address };
        } else {
            value = { LoadScalarBytes(Words(elem)[0], at) };
        }
        if (HT(owner).kind == CoreType::Limited) SetLimitedLength(shape[i.a].w[0], owner, newLen);
        else ReleaseOwnerTo(i.a, newLen, at);
        Define(i, std::move(value));
    }

    void LowerPopN(const GirInst &i) {
        auto owner = OwnerType(i.a);
        auto len = OwnerLength(i.a, owner);
        auto countType = l.IntType(HT(hvt[i.b]).ity);
        auto count = W0(i.b);
        auto countUnsigned = Conv(count, countType, U64(), CoreConvKind::AsUnchecked);
        auto lenUnsigned = Conv(len, I64(), U64(), CoreConvKind::AsUnchecked);
        auto fail = AbortBlock(GirAbortKind::PopNRange, {}, i.org);
        CheckThen(CmpI(CoreCmpOp::Le, U64(), countUnsigned, lenUnsigned), fail);
        auto countI64 = Conv(count, countType, I64(), CoreConvKind::AsUnchecked);
        auto newLen = BinW(CoreBinOp::Sub, I64(), len, countI64);
        if (HT(owner).kind == CoreType::Limited)
            SetLimitedLength(shape[i.a].w[0], owner, newLen);
        else {
            auto top = PtrAt(OwnerData(i.a, owner), newLen, Size(OwnerElement(owner)));
            ReleaseOwnerTo(i.a, newLen, top);
        }
    }

    void LowerClear(const GirInst &i) {
        auto owner = OwnerType(i.a);
        if (HT(owner).kind == CoreType::Limited) {
            SetLimitedLength(shape[i.a].w[0], owner, ConstI(I64(), 0));
            return;
        }
        auto header = shape[i.a].w[0];
        auto base = Simple(GirOp::HdrBase, Ptr(), header);
        SimpleE(GirOp::StackRelease, shape[i.a].w[1], base);
        SimpleE(GirOp::HdrSetLen, header, ConstI(I64(), 0));
    }

    void LowerResize(const GirInst &i) {
        auto owner = OwnerType(i.a);
        auto ownerKind = HT(owner).kind;
        auto elem = OwnerElement(owner);
        auto esz = Size(elem);
        auto sourceType = HT(hvt[i.b]).ity;
        auto inputType = l.IntType(sourceType);
        auto input = W0(i.b);
        auto failNegative = AbortBlock(GirAbortKind::ResizeNegative, {}, i.org);
        if (CoreIsUnsigned(sourceType)) {
            if (sourceType == CoreIntTy::U64)
                CheckThen(CmpI(CoreCmpOp::Le, U64(), input, ConstI(U64(), INT64_MAX)), failNegative);
        } else {
            CheckThen(CmpI(CoreCmpOp::Le, inputType, ConstI(inputType, 0), input), failNegative);
        }
        auto newLen = Conv(input, inputType, I64(), CoreConvKind::AsUnchecked);
        auto len = OwnerLength(i.a, owner);
        auto isGrowing = CmpI(CoreCmpOp::Gt, I64(), newLen, len);
        if (i.vals.empty()) {
            auto noFill = AbortBlock(GirAbortKind::ResizeFill, {}, i.org);
            CheckThen(CmpI(CoreCmpOp::Le, I64(), newLen, len), noFill);
        }
        if (ownerKind == CoreType::Limited && !i.vals.empty()) {
            auto capacity = AbortBlock(GirAbortKind::Capacity, {}, i.org);
            CheckThen(CmpI(CoreCmpOp::Le, I64(), newLen, ConstI(I64(), HT(owner).count)), capacity);
        }

        if (i.vals.empty()) {
            auto shrink = NewBlockL({});
            auto done = NewBlockL({});
            GirInst branch;
            branch.op = GirOp::CondBr;
            branch.a = CmpI(CoreCmpOp::Lt, I64(), newLen, len);
            branch.idx = shrink;
            branch.idx2 = done;
            Term(std::move(branch));
            cur = shrink;
            if (ownerKind == CoreType::Limited) SetLimitedLength(shape[i.a].w[0], owner, newLen);
            else {
                auto top = PtrAt(OwnerData(i.a, owner), newLen, esz);
                ReleaseOwnerTo(i.a, newLen, top);
            }
            GirInst toDone;
            toDone.op = GirOp::Br;
            toDone.idx = done;
            Term(std::move(toDone));
            cur = done;
            return;
        }

        auto shrink = NewBlockL({});
        auto equalOrGrow = NewBlockL({});
        auto grow = NewBlockL({});
        auto done = NewBlockL({});
        GirInst first;
        first.op = GirOp::CondBr;
        first.a = CmpI(CoreCmpOp::Lt, I64(), newLen, len);
        first.idx = shrink;
        first.idx2 = equalOrGrow;
        Term(std::move(first));

        cur = shrink;
        if (ownerKind == CoreType::Limited) SetLimitedLength(shape[i.a].w[0], owner, newLen);
        else {
            auto top = PtrAt(OwnerData(i.a, owner), newLen, esz);
            ReleaseOwnerTo(i.a, newLen, top);
        }
        GirInst shrinkDone;
        shrinkDone.op = GirOp::Br;
        shrinkDone.idx = done;
        Term(std::move(shrinkDone));

        cur = equalOrGrow;
        GirInst second;
        second.op = GirOp::CondBr;
        second.a = isGrowing;
        second.idx = grow;
        second.idx2 = done;
        Term(std::move(second));

        cur = grow;
        auto fill = i.vals[0];
        auto &element = HT(elem);
        int source = element.kind == CoreType::Arr || element.kind == CoreType::Struct
                         ? shape[fill].w[0]
                         : ScalarValueAddress(elem, shape[fill].w[0]);
        auto delta = BinW(CoreBinOp::Sub, I64(), newLen, len);
        auto start = PtrAt(OwnerData(i.a, owner), len, esz);
        if (ownerKind != CoreType::Limited) {
            auto bytes = BinW(CoreBinOp::Mul, I64(), delta, ConstI(I64(), esz), true, i.org);
            SimpleE(GirOp::StackBump, shape[i.a].w[1], bytes);
        }
        GirInst repeat;
        repeat.op = GirOp::BytesFill;
        repeat.a = start;
        repeat.b = source;
        repeat.idx = (int)esz;
        repeat.vals = { delta };
        EmitE(std::move(repeat));
        SetOwnerLength(i.a, owner, newLen);
        GirInst growDone;
        growDone.op = GirOp::Br;
        growDone.idx = done;
        Term(std::move(growDone));
        cur = done;
    }

    void LowerReplace(const GirInst &i) {
        auto owner = OwnerType(i.a);
        auto address = shape[i.a].w[0];
        auto stack = shape[i.a].w[1];
        auto &run = shape[i.b];
        auto elem = OwnerElement(owner);
        auto esz = Size(elem);
        auto base = Simple(GirOp::HdrBase, Ptr(), address);
        if (run.w.size() == 2) {
            auto bytes = OwnerRunBytes(owner, run.w[1]);
            CopyDynamic(base, run.w[0], bytes);
            SimpleE(GirOp::StackBump, stack, bytes);
            SimpleE(GirOp::HdrSetLen, address, run.w[1]);
            return;
        }
        for (size_t k = 0; k < run.elems.size(); k++)
            StoreAt(elem, PtrAt(base, ConstI(I64(), (int64_t)k), esz), shape[run.elems[k]].w);
        if (!run.elems.empty())
            SimpleE(GirOp::StackBump, stack, ConstI(I64(), (int64_t)run.elems.size() * esz));
        SimpleE(GirOp::HdrSetLen, address, ConstI(I64(), (int64_t)run.elems.size()));
    }

    void LowerArr(const GirInst &i) {
        auto &c = HT(i.ty);
        if (GirOwnerKind(c.kind)) {
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

    void LowerStruct(const GirInst &i) {
        auto &record = h.structs.at(HT(i.ty).structid);
        auto tmp = FrameTemp(Size(i.ty));
        auto dst = Simple(GirOp::FrameAddr, Ptr(), -1, -1, tmp);
        for (size_t k = 0; k < i.vals.size(); k++) {
            auto &field = record.fields[k];
            auto at = PtrAt(dst, ConstI(I64(), field.offset), 1);
            auto &fieldty = HT(field.type);
            if (fieldty.kind == CoreType::Arr || fieldty.kind == CoreType::Struct)
                StoreAt(field.type, at, shape[i.vals[k]].w);
            else
                StoreScalarBytes(Words(field.type)[0], at, shape[i.vals[k]].w[0]);
        }
        Define(i, { dst });
    }

    void LowerFill(const GirInst &i) {
        auto &c = HT(i.ty);
        auto esz = Size(c.elem);
        auto tmp = FrameTemp(Size(i.ty));
        auto dst = Simple(GirOp::FrameAddr, Ptr(), -1, -1, tmp);
        int src;
        auto &w = shape[i.a].w;
        if (HT(c.elem).kind == CoreType::Arr || HT(c.elem).kind == CoreType::Struct) src = w[0];
        else {
            auto one = FrameTemp(esz);
            src = Simple(GirOp::FrameAddr, Ptr(), -1, -1, one);
            if (h.profile == CoreProfile::Shrink) StoreScalarBytes(Words(c.elem)[0], src, w[0]);
            else PStoreV(Words(c.elem)[0], src, w[0]);
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
        if (lit.w.size() == 2) {
            auto bytes = OwnerRunBytes(growty, lit.w[1]);
            CopyDynamic(base, lit.w[0], bytes);
            SimpleE(GirOp::StackBump, stk, bytes);
            SimpleE(GirOp::HdrSetLen, hdr, lit.w[1]);
            return;
        }
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
                if (HT(t).kind == CoreType::Limited) InitLimited(dst, t, v);
                else if (HT(t).kind == CoreType::Slice) StoreAt(t, dst, v.w);
                else Copy(dst, v.w[0], Size(t));
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
        auto &stored = HT(hvt[i.b]);
        if (rs.unaligned && stored.kind != CoreType::Arr && stored.kind != CoreType::Struct)
            StoreScalarBytes(Words(hvt[i.b])[0], rs.w[0], v.w[0]);
        else StoreAt(hvt[i.b], rs.w[0], v.w);
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
        if (HT(rt).kind == CoreType::Arr || HT(rt).kind == CoreType::Struct) { Define(i, { tmpaddr }); return; }
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
                if (HT(rt).kind == CoreType::Arr || HT(rt).kind == CoreType::Struct) Copy(outval, v.w[0], Size(rt));
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
        } else if (HT(g.ty).kind == CoreType::Limited) {
            InitLimited(addr, g.ty, v);
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
