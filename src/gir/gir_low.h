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
        l.pointerBytes = sizeof(void *);
        l.files = h.files;
        l.diagfiles = h.diagfiles;
        l.filemodules = h.filemodules;
        l.origins = h.origins;
        l.entry = h.entry;
        // Signatures first: a call needs its callee's before its body exists.
        for (auto &f : h.funcs) lsigs.push_back(Signature(f));
        for (auto &target : h.targets) {
            GirLowTarget low;
            low.members = target.members;
            low.cells.push_back(l.BoolType());
            auto &function = h.funcs[target.members[0]];
            auto &signature = lsigs[target.members[0]];
            for (size_t result = 0; result < function.results.size(); result++) {
                GirLowChannel channel;
                channel.position = (int)result;
                for (auto word : signature.resultWords[result]) {
                    (void)word;
                    channel.incoming.push_back((int)low.cells.size());
                    low.cells.push_back(Ptr());
                }
                auto escaped = GirNonfixed(h, function.results[result]) ? vector<GirTypeId> { Ptr(), Ptr(), I64() } : signature.resultWords[result];
                for (auto word : escaped) {
                    channel.escaped.push_back((int)low.cells.size());
                    low.cells.push_back(word);
                }
                low.channels.push_back(std::move(channel));
            }
            l.lowtargets.push_back(std::move(low));
        }
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
        vector<vector<GirTypeId>> resultWords;
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
            case CoreType::Arr: case CoreType::VarArr: return { Ptr() };
            case CoreType::Dest: case CoreType::Built: case CoreType::Cancelled: return { Ptr(), Ptr(), Ptr() };
            case CoreType::Tuple: {
                vector<GirTypeId> words;
                for (auto part : c.parts) { auto value = Words(part); words.insert(words.end(), value.begin(), value.end()); }
                return words;
            }
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
        if (CoreHasConstruction(h.profile)) {
            for (auto parameter : f.params)
                for (auto word : GirNonfixed(h, parameter) ? vector<GirTypeId> { Ptr(), Ptr() } : Words(parameter)) s.params.push_back(word);
            for (auto result : f.results) {
                auto words = GirNonfixed(h, result) ? vector<GirTypeId> { Ptr(), Ptr(), Ptr() } : Words(result);
                s.resultWords.push_back(words);
                for (size_t word = 0; word < words.size(); word++) s.params.push_back(Ptr());
            }
            return s;
        }
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
        if (k == CoreType::VarArr || (k == CoreType::Arr && GirNonfixed(h, g.ty))) {
            out.kind = GirMember::Dynamic;
            out.stack = l.globalstacks;
            gstack.push_back(l.globalstacks++);
        } else if (k == CoreType::Arr || k == CoreType::Struct || k == CoreType::Limited) {
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
        int source = -1;
    };

    struct Place {
        enum Kind { Scalar, Bytes, Header, Dynamic, Alias, Words } kind = Scalar;
        vector<int> members;
        int stack = -1;
    };

    struct Destination {
        int header = -1;
        int stack = -1;
        int base = -1;
        int metadata = -1;
        GirTypeId type = -1;
        CoreRequest request = CoreRequest::Value;
        int receiverSlot = -1;
        int receiverReference = -1;
        int receiverGlobal = -1;
        int oldLength = -1;
        bool push = false;
        bool append = false;
        bool privateSource = false;
        int source = -1;
        int resultPosition = -1;
        int target = -1;
        int payloadEndMember = -1;
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
    map<int, Destination> destinations;
    map<int, Destination> completions;
    vector<int> carrierRoots;
    map<int, int> payloadEndMembers;
    map<int, int> scratchStacks;
    map<const GirInst *, int> printStacks;
    map<int, Destination> namedDestinations;
    map<int, pair<int, int>> ownedArguments;
    map<int, vector<int>> callResultSources;
    vector<int> sourceMembers, referenceSources;
    vector<int> sourceParameterPositions;
    vector<vector<int>> resultOutputPositions;
    int sourceScope = -1;
    map<int, vector<int>> savedTargets;
    map<int, int> targetTokens;
    map<int, vector<int>> protectedCarriers;
    set<int> forwardingReferences;
    vector<int> protectedStacks;
    vector<GirTypeId> lvals;
    int cur = -1;
    int spval = 0, outval = -1;
    vector<vector<int>> resultOutputs;
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

    int TraceId(GirTraceKind kind) {
        GirInst id;
        id.op = GirOp::TraceId;
        id.trace = kind;
        return Emit(std::move(id), I64());
    }

    void Event(GirEventKind kind, vector<int> operands, GirEventReason reason = GirEventReason::None) {
        GirInst event;
        event.op = GirOp::Event;
        event.event = kind;
        event.reason = reason;
        event.vals = std::move(operands);
        EmitE(std::move(event));
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
        return (kind == CoreType::Arr && !GirNonfixed(h, ty)) || kind == CoreType::Struct;
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
        if (CoreHasConstruction(h.profile))
            for (size_t position = 0; position < params.size(); position++) if (GirRefLike(h, params[position].second) && !forwardingReferences.count(params[position].first)) {
                auto source = shape[values[position]].source;
                if (source < 0) throw CompileError { "reference branch omits its source metadata" };
                words.push_back(source);
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

    void BranchProduced(int target, const vector<Shape> &produced, const vector<int> &forwarded) {
        vector<Shape> saved;
        vector<int> values;
        auto &parameters = hf->blocks[target].params;
        for (size_t position = 0; position < produced.size(); position++) {
            auto parameter = parameters[position].first;
            saved.push_back(shape[parameter]);
            shape[parameter] = produced[position];
            values.push_back(parameter);
        }
        values.insert(values.end(), forwarded.begin(), forwarded.end());
        LowerBranch(target, values);
        for (size_t position = 0; position < produced.size(); position++) shape[parameters[position].first] = std::move(saved[position]);
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
        sourceMembers.assign(hf->slots.size(), -1);
        referenceSources.assign(hf->slots.size(), -1);
        scratchStacks.clear();
        printStacks.clear();
        scopeheaders.assign(hf->scopes.size(), {});
        int stacks = 0;
        for (size_t s = 0; s < hf->slots.size(); s++) {
            auto &sl = hf->slots[s];
            auto &c = HT(sl.ty);
            auto &p = places[s];
            auto name = cat("s", s);
            bool ownedParameter = false;
            if (CoreHasConstruction(h.profile) && GirNonfixed(h, sl.ty))
                for (auto &instruction : hf->blocks[0].insts)
                    if (instruction.op == GirOp::Init && instruction.idx == (int)s)
                        for (size_t parameter = 0; parameter < hf->params.size(); parameter++)
                            if (hf->params[parameter] == sl.ty && instruction.a == hf->blocks[0].params[parameter].first)
                                ownedParameter = true;
            bool namedResult = false;
            for (auto &protocol : hf->resultProtocols) namedResult |= protocol.namedSlot == (int)s;
            if (ownedParameter || namedResult) {
                p.kind = Place::Alias;
                for (int word = 0; word < 2; word++) {
                    GirMember member;
                    member.kind = GirMember::Scalar;
                    member.ty = Ptr();
                    member.scope = sl.scope;
                    member.name = name;
                    p.members.push_back(Member(std::move(member)));
                }
            } else if (c.kind == CoreType::VarArr || (c.kind == CoreType::Arr && GirNonfixed(h, sl.ty))) {
                p.kind = Place::Dynamic;
                p.stack = stacks++;
                GirMember member;
                member.kind = GirMember::Dynamic;
                member.stack = p.stack;
                member.scope = sl.scope;
                member.name = name;
                p.members = { Member(std::move(member)) };
                scopeheaders[sl.scope].push_back((int)s);
            } else if (c.kind == CoreType::Arr || c.kind == CoreType::Struct) {
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
        if (CoreHasConstruction(h.profile)) {
            for (auto &block : hf->blocks) for (auto &instruction : block.insts)
                if ((instruction.op == GirOp::DestOpen && holds_alternative<GirDestArgReceiver>(instruction.destReceiver)) ||
                    instruction.op == GirOp::Render)
                    scratchStacks[instruction.res] = stacks++;
            for (auto &block : hf->blocks) for (auto &instruction : block.insts)
                if (instruction.op == GirOp::Print) printStacks[&instruction] = stacks++;
            for (size_t slot = 0; slot < places.size(); slot++) {
                GirMember source;
                source.kind = GirMember::Scalar;
                source.ty = Ptr();
                source.scope = hf->slots[slot].scope;
                source.name = "source";
                sourceMembers[slot] = Member(source);
                source.name = "reference_source";
                referenceSources[slot] = Member(std::move(source));
            }
        }
        set<int> scratchOwned;
        for (auto &[value, stack] : scratchStacks) scratchOwned.insert(stack);
        for (auto &[instruction, stack] : printStacks) scratchOwned.insert(stack);
        for (auto stack : scratchOwned) {
            GirMember member;
            member.kind = GirMember::Dynamic;
            member.stack = stack;
            member.scope = 0;
            member.name = "scratch";
            Member(std::move(member));
        }
        lf.stacks = stacks;
    }

    GirFunc LowerFunc(const GirFunc &f, int global) {
        hf = &f;
        initglobal = global;
        lf = GirFunc {};
        if (CoreHasConstruction(h.profile)) lf.lowResults.emplace();
        lf.name = f.name;
        lf.org = f.org;
        lf.key = f.key;
        lf.module = f.module;
        lf.summary.unknown = true;   // Effects are a property of the high stage.
        lvals.clear();
        marks.clear();
        shape.clear();
        destinations.clear();
        payloadEndMembers.clear();
        completions.clear();
        resultOutputs.clear();
        resultOutputPositions.clear();
        sourceParameterPositions.clear();
        sourceScope = -1;
        savedTargets.clear();
        targetTokens.clear();
        protectedCarriers.clear();
        forwardingReferences.clear();
        protectedStacks.clear();
        namedDestinations.clear();
        ownedArguments.clear();
        callResultSources.clear();
        // Value types of the high function.
        ComputeTypes();
        ComputeCarrierRoots();
        for (auto &block : f.blocks) for (auto &inst : block.insts) if (inst.op == GirOp::Invoke) {
            for (auto &edge : inst.escapes) {
                auto &target = h.targets[edge.target];
                auto &results = h.funcs[target.members[0]].results;
                for (size_t result = 0; result < results.size(); result++) {
                    auto parameter = f.blocks[edge.block].params[result].first;
                    if (GirNonfixed(h, results[result])) protectedCarriers[edge.block].push_back(parameter);
                    else if (GirRefLike(h, results[result]) && !HandlesTarget(edge.target)) forwardingReferences.insert(parameter);
                }
            }
        }
        PlaceSlots();
        // Signature.
        Sig initsig;
        if (global >= 0) { initsig = Signature(f); initsig.params = { I64() }; }
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
        if (CoreHasShrink(h.profile))
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
            if (b > 0 && CoreHasConstruction(h.profile))
                for (auto &p : f.blocks[b].params) if (GirRefLike(h, p.second) && !forwardingReferences.count(p.first)) ps.push_back(Ptr());
            vector<int> ids;
            bmap[b] = NewBlockL(ps, &ids);
            if (b == 0) {
                spval = ids[0];
                size_t k = 1;
                outval = -1;
                if (global < 0 && sig->out) outval = ids[k++];
                for (size_t parameter = 0; parameter < f.params.size(); parameter++) {
                    auto &p = f.blocks[0].params[parameter];
                    sourceParameterPositions.push_back((int)k);
                    auto words = GirNonfixed(h, f.params[parameter]) ? vector<GirTypeId> { Ptr(), Ptr() } : Words(p.second);
                    for (auto word : words) { (void)word; shape[p.first].w.push_back(ids[k++]); }
                }
                if (CoreHasConstruction(h.profile)) {
                    size_t incoming = f.params.size();
                    for (size_t result = 0; result < f.results.size(); result++) {
                        vector<int> outputs, positions;
                        if (global >= 0) {
                            outputs = {};
                        } else for (size_t word = 0; word < sig->resultWords[result].size(); word++) { positions.push_back((int)k); outputs.push_back(ids[k++]); }
                        resultOutputs.push_back(outputs);
                        resultOutputPositions.push_back(positions);
                        if (global < 0) {
                            auto type = f.results[result];
                            auto kind = HT(type).kind;
                            if (GirNonfixed(h, type))
                                lf.lowResults->push_back({ type, GirLowNonfixedResult { f.resultProtocols[result].request,
                                    positions[0], positions[1], positions[2] } });
                            else if (IsAggregate(type))
                                lf.lowResults->push_back({ type, GirLowSnapshotResult { Size(type), positions[0] } });
                            else if (kind == CoreType::Ref) {
                                if (positions.size() == 2)
                                    lf.lowResults->push_back({ type, GirLowResizableReferenceResult { positions[0], positions[1] } });
                                else lf.lowResults->push_back({ type, GirLowReferenceResult { positions[0] } });
                            } else if (kind == CoreType::Slice)
                                lf.lowResults->push_back({ type, GirLowSliceResult { positions[0], positions[1] } });
                            else if (!positions.empty())
                                lf.lowResults->push_back({ type, GirLowScalarResult { sig->resultWords[result][0], positions[0] } });
                        }
                        if (GirNonfixed(h, f.results[result]) && global < 0)
                            shape[f.blocks[0].params[incoming++].first].w = outputs;
                    }
                }
            } else {
                size_t k = 0;
                for (auto &p : f.blocks[b].params)
                    if (!IsAggregate(p.second) && !IsOwnerRun(p.second))
                        for (auto t : Words(p.second)) { (void)t; shape[p.first].w.push_back(ids[k++]); }
                if (CoreHasConstruction(h.profile))
                    for (auto &p : f.blocks[b].params) if (GirRefLike(h, p.second) && !forwardingReferences.count(p.first)) shape[p.first].source = ids[k++];
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
            else if (t.op == GirOp::Invoke) {
                succ.push_back(t.a);
                for (auto &edge : t.escapes) succ.push_back(edge.block);
            }
            for (auto s : succ) if (!state[s]) dfs(s);
            order.push_back(b);
        };
        dfs(0);
        reverse(order.begin(), order.end());
        for (auto b : order) {
            cur = bmap[b];
            protectedStacks.clear();
            for (auto value : protectedCarriers[b]) protectedStacks.push_back(shape[value].w[0]);
            if (b == 0 && CoreHasConstruction(h.profile)) {
                sourceScope = Simple(GirOp::SourceEnter, Ptr());
                for (size_t parameter = 0; parameter < f.params.size(); parameter++) {
                    auto type = f.params[parameter];
                    if (HT(type).kind == CoreType::Ref || GirNonfixed(h, type))
                        shape[f.blocks[0].params[parameter].first].source = Simple(GirOp::SourceParam, Ptr(), -1, -1, sourceParameterPositions[parameter]);
                }
            }
            if (b == 0 && CoreHasConstruction(h.profile)) {
                size_t incoming = f.params.size();
                for (size_t result = 0; result < f.results.size(); result++) {
                    if (!GirNonfixed(h, f.results[result])) continue;
                    auto value = f.blocks[0].params[incoming++].first;
                    Destination destination;
                    destination.type = f.results[result];
                    destination.request = f.resultProtocols[result].request;
                    destination.resultPosition = (int)result;
                    if (global >= 0) {
                        auto receiver = l.lowglobals[global].kind;
                        destination.stack = Simple(GirOp::GlobalStack, Ptr(), -1, -1, global);
                        destination.base = Simple(GirOp::StackMark, Ptr(), destination.stack);
                        destination.metadata = Metadata(TraceId(GirTraceKind::Destination));
                        destination.receiverGlobal = global;
                        destination.source = NewSource(TraceId(GirTraceKind::Storage));
                        SimpleE(GirOp::SourceGlobalSet, destination.source, -1, global);
                        if (receiver == GirMember::Header) destination.header = Simple(GirOp::GlobalAddr, Ptr(), -1, -1, global);
                        shape[value].w = { destination.stack, destination.base, destination.metadata };
                        destinations[carrierRoots[value]] = destination;
                        Event(GirEventKind::Begin, { DestinationId(value) });
                        StartPrefix(value);
                    } else {
                        destination.stack = shape[value].w[0];
                        destination.base = shape[value].w[1];
                        destination.metadata = shape[value].w[2];
                    }
                    destinations[carrierRoots[value]] = destination;
                }
                if (global < 0) EnterTargets();
            }
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
        if (lf.scopes.empty()) lf.scopes.push_back(-1);
        lf.blocks.shrink_to_fit();
        return std::move(lf);
    }

    int FuncIndex(const GirFunc &f) {
        return (int)(&f - h.funcs.data());
    }

    bool HandlesTarget(int target) const {
        auto &members = h.targets[target].members;
        auto function = (int)(hf - h.funcs.data());
        return initglobal < 0 && find(members.begin(), members.end(), function) != members.end();
    }

    int TargetCell(int target, int cell) {
        GirInst load;
        load.op = GirOp::TargetLoad;
        load.idx = target;
        load.idx2 = cell;
        return Emit(std::move(load), l.lowtargets[target].cells[cell]);
    }

    void SetTargetCell(int target, int cell, int value) {
        GirInst store;
        store.op = GirOp::TargetStore;
        store.idx = target;
        store.idx2 = cell;
        store.a = value;
        EmitE(std::move(store));
    }

    void EnterTargets() {
        for (size_t target = 0; target < h.targets.size(); target++) {
            if (!HandlesTarget((int)target)) continue;
            auto &table = l.lowtargets[target];
            for (size_t cell = 0; cell < table.cells.size(); cell++)
                savedTargets[(int)target].push_back(TargetCell((int)target, (int)cell));
            SetTargetCell((int)target, 0, ConstBool(true));
            GirInst enter;
            enter.op = GirOp::SourceTargetEnter;
            enter.idx = (int)target;
            for (size_t result = 0; result < table.channels.size(); result++) {
                auto &channel = table.channels[result];
                for (size_t word = 0; word < channel.incoming.size(); word++)
                    SetTargetCell((int)target, channel.incoming[word], resultOutputs[result][word]);
                enter.vals.push_back(HT(hf->results[result]).kind == CoreType::Ref ? resultOutputPositions[result][0] : -1);
            }
            targetTokens[(int)target] = Emit(std::move(enter), Ptr());
        }
    }

    void LeaveTargets() {
        for (auto target = savedTargets.rbegin(); target != savedTargets.rend(); ++target) {
            SimpleE(GirOp::SourceTargetLeave, targetTokens.at(target->first));
            for (size_t cell = 0; cell < target->second.size(); cell++)
                SetTargetCell(target->first, (int)cell, target->second[cell]);
        }
    }

    void ReleaseUnprotected(int stack, int mark) {
        if (protectedStacks.empty()) { SimpleE(GirOp::StackRelease, stack, mark); return; }
        auto release = NewBlockL({});
        auto done = NewBlockL({});
        for (auto protectedStack : protectedStacks) {
            auto next = NewBlockL({});
            GirInst branch;
            branch.op = GirOp::CondBr;
            branch.a = Simple(GirOp::PtrEq, l.BoolType(), stack, protectedStack);
            branch.idx = done;
            branch.idx2 = next;
            Term(std::move(branch));
            cur = next;
        }
        GirInst jump;
        jump.op = GirOp::Br;
        jump.idx = release;
        Term(std::move(jump));
        cur = release;
        SimpleE(GirOp::StackRelease, stack, mark);
        jump = GirInst {};
        jump.op = GirOp::Br;
        jump.idx = done;
        Term(std::move(jump));
        cur = done;
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
                    GirTyEnv env { mm, f.slots, hsigs, hvt, nullptr, &f.blocks, &f };
                    auto r = GirTyper(env).Of(i);
                    if (r.ok()) { hvt[i.res] = r.ty; changed = true; }
                }
        }
    }

    // ---------------------------------------------------------------------
    // Instructions.

    void Define(const GirInst &i, vector<int> words) { shape[i.res].w = std::move(words); }

    void ComputeCarrierRoots() {
        carrierRoots.resize(hvt.size());
        for (size_t value = 0; value < carrierRoots.size(); value++) carrierRoots[value] = (int)value;
        auto carrier = [&](int value) {
            auto kind = HT(hvt[value]).kind;
            return kind == CoreType::Dest || kind == CoreType::Built || kind == CoreType::Cancelled;
        };
        for (auto changed = true; changed;) {
            changed = false;
            auto link = [&](int from, int to) {
                if (carrierRoots[to] != carrierRoots[from]) { carrierRoots[to] = carrierRoots[from]; changed = true; }
            };
            for (auto &block : hf->blocks) for (auto &inst : block.insts) {
                if (inst.op == GirOp::CallConstruct && HT(hvt[inst.res]).kind == CoreType::Built)
                    link(inst.vals2[0], inst.res);
                if (inst.op == GirOp::Result && carrier(inst.res)) {
                    for (auto &producerBlock : hf->blocks) for (auto &producer : producerBlock.insts)
                        if (producer.res == inst.a && producer.op == GirOp::CallConstruct) {
                            size_t channel = 0;
                            for (int position = 0; position < inst.idx; position++)
                                if (GirNonfixed(h, h.funcs[producer.idx].results[position])) channel++;
                            link(producer.vals2[channel], inst.res);
                        }
                }
                if (inst.op == GirOp::DestFinish || inst.op == GirOp::DestAbandon || inst.op == GirOp::DestValue ||
                    inst.op == GirOp::DestStage || inst.op == GirOp::DestFit || inst.op == GirOp::DestRelocate ||
                    inst.op == GirOp::DestAdapt || inst.op == GirOp::DestAdaptFinish)
                    link(inst.a, inst.res);
                auto edge = [&](int target, const vector<int> &values) {
                    for (size_t position = 0; position < values.size(); position++)
                        if (carrier(values[position])) link(values[position], hf->blocks[target].params[position].first);
                };
                if (inst.op == GirOp::Br || inst.op == GirOp::CondBr) edge(inst.idx, inst.vals);
                if (inst.op == GirOp::CondBr) edge(inst.idx2, inst.vals2);
                if (inst.op == GirOp::Invoke) {
                    auto &callee = h.funcs[inst.idx];
                    size_t channel = 0;
                    for (size_t result = 0; result < callee.results.size(); result++)
                        if (GirNonfixed(h, callee.results[result])) link(inst.vals2[channel++], hf->blocks[inst.a].params[result].first);
                    for (auto &escape : inst.escapes) {
                        auto leading = h.funcs[h.targets[escape.target].members[0]].results.size();
                        for (size_t normal = 0; normal < inst.vals2.size(); normal++)
                            link(inst.vals2[normal], hf->blocks[escape.block].params[leading + normal].first);
                    }
                }
            }
        }
    }

    int NewSource(int storage) { return Simple(GirOp::SourceNew, Ptr(), storage); }
    int ChildSource(int source, int index) {
        if (source < 0) throw CompileError { "derived reference has no storage source" };
        return Simple(GirOp::SourceChild, Ptr(), source, index);
    }
    int CreateObject(int slot) {
        auto storage = TraceId(GirTraceKind::Storage);
        auto source = NewSource(storage);
        SimpleE(GirOp::LocalSet, source, -1, sourceMembers[slot]);
        return source;
    }

    int Metadata(int trace) {
        auto address = Simple(GirOp::FrameAddr, Ptr(), -1, -1, FrameTemp(16));
        PStoreV(I64(), address, ConstI(I64(), 0));
        PStoreV(I64(), WordAt(address, 1), trace);
        return address;
    }

    Destination DestinationAt(int value) {
        auto destination = destinations.at(carrierRoots.at(value));
        if (shape[value].w.size() == 3) {
            destination.stack = shape[value].w[0];
            destination.base = shape[value].w[1];
            destination.metadata = shape[value].w[2];
        }
        return destination;
    }

    int DestinationCount(int value) { return PLoadV(I64(), shape[value].w[2]); }
    int DestinationId(int value) { return PLoadV(I64(), WordAt(shape[value].w[2], 1)); }
    int Prefix(GirTypeId type, CoreRequest request) const {
        return HT(type).kind == CoreType::VarArr && request == CoreRequest::Value ? 4 : 0;
    }

    void StartPrefix(int value) {
        auto destination = DestinationAt(value);
        auto prefix = Prefix(HT(hvt[value]).elem, HT(hvt[value]).request);
        if (prefix) SimpleE(GirOp::StackBump, destination.stack, ConstI(I64(), prefix));
    }

    void PatchPrefix(int value, int org) {
        auto &carrier = HT(hvt[value]);
        if (Prefix(carrier.elem, carrier.request)) {
            auto count = DestinationCount(value);
            CheckThen(CmpI(CoreCmpOp::Le, U64(), Conv(count, I64(), U64()), ConstI(U64(), UINT32_MAX)),
                      AbortBlock(GirAbortKind::Capacity, {}, org));
            StoreScalarBytes(l.IntType(CoreIntTy::U32), shape[value].w[1],
                             Conv(count, I64(), l.IntType(CoreIntTy::U32)));
        }
    }

    void IncrementDestination(int value) {
        auto count = DestinationCount(value);
        Event(GirEventKind::Write, { DestinationId(value), count });
        PStoreV(I64(), shape[value].w[2], BinW(CoreBinOp::Add, I64(), count, ConstI(I64(), 1)));
    }

    void Open(const GirInst &inst) {
        Destination destination;
        destination.type = inst.ty;
        destination.request = inst.request;
        destination.metadata = Metadata(TraceId(GirTraceKind::Destination));
        if (auto slot = get_if<GirDestSlotReceiver>(&inst.destReceiver)) {
            destination.receiverSlot = slot->slot;
            auto &place = places.at(slot->slot);
            destination.source = CreateObject(slot->slot);
            destination.stack = StackOf(place.stack);
            if (place.kind == Place::Header) destination.header = Simple(GirOp::FrameAddr, Ptr(), -1, -1, place.members[0]);
        } else if (auto global = get_if<GirDestGlobalReceiver>(&inst.destReceiver)) {
            destination.receiverGlobal = global->global;
            destination.stack = Simple(GirOp::GlobalStack, Ptr(), -1, -1, global->global);
            if (l.lowglobals[global->global].kind == GirMember::Header)
                destination.header = Simple(GirOp::GlobalAddr, Ptr(), -1, -1, global->global);
        } else if (holds_alternative<GirDestArgReceiver>(inst.destReceiver)) {
            destination.stack = StackOf(scratchStacks.at(inst.res));
            destination.privateSource = true;
            destination.source = NewSource(TraceId(GirTraceKind::Storage));
        } else {
            int reference = -1;
            if (auto whole = get_if<GirDestWholeReceiver>(&inst.destReceiver)) reference = whole->reference;
            if (auto append = get_if<GirDestAppendReceiver>(&inst.destReceiver)) { reference = append->reference; destination.append = true; }
            if (auto push = get_if<GirDestPushReceiver>(&inst.destReceiver)) { reference = push->reference; destination.push = true; }
            destination.receiverReference = reference;
            destination.header = shape[reference].w[0];
            destination.stack = shape[reference].w[1];
            if (destination.append || destination.push) destination.oldLength = Simple(GirOp::HdrLen, I64(), destination.header);
        }
        destination.base = Simple(GirOp::StackMark, Ptr(), destination.stack);
        destinations[carrierRoots[inst.res]] = destination;
        Define(inst, { destination.stack, destination.base, destination.metadata });
        Event(GirEventKind::Begin, { DestinationId(inst.res) });
        if (destination.header >= 0 && !destination.append && !destination.push)
            SimpleE(GirOp::HdrInit, destination.header, destination.base);
        StartPrefix(inst.res);
    }

    void WriteFixed(int destination, GirTypeId element, const vector<int> &words) {
        auto stack = shape[destination].w[0];
        auto address = Simple(GirOp::StackMark, Ptr(), stack);
        SimpleE(GirOp::StackBump, stack, ConstI(I64(), Size(element)));
        StoreAt(element, address, words);
        IncrementDestination(destination);
    }

    int WalkElements(GirTypeId element, int base, int count) {
        if (GirFlat(h, element)) return BinW(CoreBinOp::Mul, I64(), count, ConstI(I64(), Size(element)));
        vector<int> arguments;
        auto loop = NewBlockL({ I64(), I64() }, &arguments);
        vector<int> finished;
        auto done = NewBlockL({ I64() }, &finished);
        auto body = NewBlockL({});
        GirInst start;
        start.op = GirOp::Br;
        start.idx = loop;
        start.vals = { ConstI(I64(), 0), ConstI(I64(), 0) };
        Term(std::move(start));
        cur = loop;
        GirInst branch;
        branch.op = GirOp::CondBr;
        branch.a = CmpI(CoreCmpOp::Lt, I64(), arguments[0], count);
        branch.idx = body;
        branch.idx2 = done;
        branch.vals2 = { arguments[1] };
        Term(std::move(branch));
        cur = body;
        auto address = PtrAt(base, arguments[1], 1);
        auto size = WalkValue(element, address);
        auto bytes = BinW(CoreBinOp::Add, I64(), arguments[1], size);
        auto next = BinW(CoreBinOp::Add, I64(), arguments[0], ConstI(I64(), 1));
        GirInst again;
        again.op = GirOp::Br;
        again.idx = loop;
        again.vals = { next, bytes };
        Term(std::move(again));
        cur = done;
        return finished[0];
    }

    int WalkValue(GirTypeId type, int start) {
        if (GirFlat(h, type)) return ConstI(I64(), Size(type));
        auto &array = HT(type);
        auto prefix = array.kind == CoreType::VarArr ? 4 : 0;
        auto count = prefix ? Conv(LoadScalarBytes(l.IntType(CoreIntTy::U32), start), l.IntType(CoreIntTy::U32), I64()) : ConstI(I64(), array.count);
        auto elements = WalkElements(array.elem, PtrAt(start, ConstI(I64(), prefix), 1), count);
        return prefix ? BinW(CoreBinOp::Add, I64(), ConstI(I64(), prefix), elements) : elements;
    }

    int ElementAt(GirTypeId element, int base, int index) {
        return GirFlat(h, element) ? PtrAt(base, index, Size(element)) : PtrAt(base, WalkElements(element, base, index), 1);
    }

    void ForCount(int count, const function<void(int)> &body) {
        vector<int> index;
        auto header = NewBlockL({ I64() }, &index);
        auto iteration = NewBlockL({});
        auto done = NewBlockL({});
        GirInst enter;
        enter.op = GirOp::Br;
        enter.idx = header;
        enter.vals = { ConstI(I64(), 0) };
        Term(std::move(enter));
        cur = header;
        GirInst branch;
        branch.op = GirOp::CondBr;
        branch.a = CmpI(CoreCmpOp::Lt, I64(), index[0], count);
        branch.idx = iteration;
        branch.idx2 = done;
        Term(std::move(branch));
        cur = iteration;
        body(index[0]);
        auto next = BinW(CoreBinOp::Add, I64(), index[0], ConstI(I64(), 1));
        GirInst again;
        again.op = GirOp::Br;
        again.idx = header;
        again.vals = { next };
        Term(std::move(again));
        cur = done;
    }

    pair<int, int> Sample(int value) {
        auto type = HT(hvt[value]);
        if (type.kind == CoreType::View || type.kind == CoreType::Slice)
            return { shape[value].w[0], shape[value].w[1] };
        auto owner = type.kind == CoreType::Ref ? type.elem : hvt[value];
        auto address = shape[value].w[0];
        auto &array = HT(owner);
        if (array.kind == CoreType::Slice)
            return { PLoadV(Ptr(), address), PLoadV(I64(), WordAt(address, 1)) };
        if (array.kind == CoreType::VarArr)
            return { PtrAt(address, ConstI(I64(), 4), 1), Conv(LoadScalarBytes(l.IntType(CoreIntTy::U32), address), l.IntType(CoreIntTy::U32), I64()) };
        if (array.kind == CoreType::Arr) return { address, ConstI(I64(), array.count) };
        if (array.kind == CoreType::Limited) return { LimitedData(address, owner), LimitedLength(address, owner) };
        return { Simple(GirOp::HdrBase, Ptr(), address), Simple(GirOp::HdrLen, I64(), address) };
    }

    void CopyRun(int destination, int source, int count, GirTypeId element) {
        ForCount(count, [&](int index) {
            auto address = ElementAt(element, source, index);
            auto bytes = WalkValue(element, address);
            auto stack = shape[destination].w[0];
            auto target = Simple(GirOp::StackMark, Ptr(), stack);
            SimpleE(GirOp::StackBump, stack, bytes);
            CopyDynamic(target, address, bytes);
            IncrementDestination(destination);
        });
    }

    void CopyDestination(const GirInst &inst) {
        auto [base, count] = Sample(inst.b);
        auto element = HT(HT(hvt[inst.a]).elem).elem;
        if (shape[inst.b].source < 0) throw CompileError { "construction copy has no retained storage source" };
        SimpleE(GirOp::SourceCopy, shape[inst.b].source, DestinationId(inst.a));
        CopyRun(inst.a, base, count, element);
    }

    void RepeatDestination(const GirInst &inst) {
        auto &array = HT(HT(hvt[inst.a]).elem);
        auto source = shape[inst.b].w[1];
        auto bytes = WalkValue(array.elem, source);
        ForCount(ConstI(I64(), array.count), [&](int) {
            auto stack = shape[inst.a].w[0];
            auto target = Simple(GirOp::StackMark, Ptr(), stack);
            SimpleE(GirOp::StackBump, stack, bytes);
            CopyDynamic(target, source, bytes);
            Event(GirEventKind::Copy, { DestinationId(inst.b), DestinationId(inst.a) }, GirEventReason::Repeat);
            IncrementDestination(inst.a);
        });
        SimpleE(GirOp::StackRelease, shape[inst.b].w[0], shape[inst.b].w[1]);
    }

    void Publish(int value, int org) {
        auto destination = DestinationAt(value);
        auto count = DestinationCount(value);
        if (destination.push) count = ConstI(I64(), 1);
        if (destination.append || destination.push) count = BinW(CoreBinOp::Add, I64(), destination.oldLength, count, true, org);
        if (destination.header >= 0) SimpleE(GirOp::HdrSetLen, destination.header, count);
        if (destination.receiverSlot >= 0 && places[destination.receiverSlot].kind == Place::Dynamic)
            SimpleE(GirOp::LocalSet, shape[value].w[1], -1, places[destination.receiverSlot].members[0]);
        if (destination.receiverGlobal >= 0 && l.lowglobals[destination.receiverGlobal].kind == GirMember::Dynamic)
            PStoreV(Ptr(), Simple(GirOp::GlobalAddr, Ptr(), -1, -1, destination.receiverGlobal), shape[value].w[1]);
        Event(GirEventKind::Publish, { DestinationId(value) });
    }

    void AdaptDestination(const GirInst &inst) {
        shape[inst.res] = shape[inst.a];
        auto &before = HT(hvt[inst.a]);
        auto &after = HT(hvt[inst.res]);
        if (inst.op == GirOp::DestAdapt) {
            auto receivingPrefix = Prefix(before.elem, before.request);
            auto producerPrefix = Prefix(after.elem, after.request);
            if (receivingPrefix > producerPrefix)
                shape[inst.res].w[1] = PtrAt(shape[inst.a].w[1], ConstI(I64(), receivingPrefix - producerPrefix), 1);
            if (producerPrefix > receivingPrefix)
                SimpleE(GirOp::StackBump, shape[inst.a].w[0], ConstI(I64(), producerPrefix - receivingPrefix));
            return;
        }
        if (inst.op == GirOp::DestAdaptFinish) {
            auto producerPrefix = Prefix(before.elem, before.request);
            auto receivingPrefix = Prefix(after.elem, after.request);
            if (receivingPrefix > producerPrefix)
                shape[inst.res].w[1] = PtrAt(shape[inst.a].w[1], ConstI(I64(), producerPrefix - receivingPrefix), 1);
            if (before.kind == CoreType::Cancelled) return;
            if (producerPrefix > receivingPrefix) {
                auto start = shape[inst.a].w[1];
                auto source = PtrAt(start, ConstI(I64(), producerPrefix - receivingPrefix), 1);
                auto bytes = WalkElements(HT(before.elem).elem, source, DestinationCount(inst.a));
                GirInst move;
                move.op = GirOp::BytesMove;
                move.a = start;
                move.b = source;
                move.vals = { bytes };
                EmitE(std::move(move));
                SimpleE(GirOp::StackRelease, shape[inst.a].w[0], PtrAt(start, bytes, 1));
                Event(GirEventKind::Relocate, { DestinationId(inst.a) }, GirEventReason::HeaderRemoval);
            }
            PatchPrefix(inst.res, inst.org);
            return;
        }
        if (inst.op == GirOp::DestValue) {
            if (Prefix(after.elem, after.request)) StartPrefix(inst.res);
            return;
        }
        if (inst.op == GirOp::DestStage || inst.op == GirOp::DestFit)
            throw GirLowerUnsupported { "limited-stage", hf->name, inst.org };
        if (inst.op == GirOp::DestRelocate && inst.reason == GirEventReason::HeaderRemoval) {
            auto prefix = Prefix(before.elem, before.request);
            if (prefix) {
                auto count = DestinationCount(inst.a);
                auto start = shape[inst.a].w[1];
                auto source = PtrAt(start, ConstI(I64(), prefix), 1);
                auto bytes = WalkElements(HT(before.elem).elem, source, count);
                GirInst move;
                move.op = GirOp::BytesMove;
                move.a = start;
                move.b = source;
                move.vals = { bytes };
                EmitE(std::move(move));
                SimpleE(GirOp::StackRelease, shape[inst.a].w[0], PtrAt(start, bytes, 1));
            }
        } else if (inst.op == GirOp::DestRelocate && inst.reason == GirEventReason::ExitValue) {
            auto destination = DestinationAt(inst.a);
            if (destination.resultPosition < 0) throw CompileError { "exit value has no matching receiving channel" };
            auto target = resultOutputs.at(destination.resultPosition)[1];
            auto prefix = Prefix(before.elem, before.request);
            auto count = DestinationCount(inst.a);
            auto bytes = WalkElements(HT(before.elem).elem, PtrAt(shape[inst.a].w[1], ConstI(I64(), prefix), 1), count);
            bytes = BinW(CoreBinOp::Add, I64(), bytes, ConstI(I64(), prefix));
            if (destination.target >= 0) {
                if (destination.payloadEndMember < 0) throw CompileError { "target landing omits its escaped endpoint" };
                auto end = Simple(GirOp::LocalGet, Ptr(), -1, -1, destination.payloadEndMember);
                auto computedEnd = PtrAt(shape[inst.a].w[1], bytes, 1);
                CheckThen(Simple(GirOp::PtrEq, l.BoolType(), computedEnd, end),
                    AbortBlock(GirAbortKind::Assert, {}, inst.org));
            }
            GirInst move;
            move.op = GirOp::BytesMove;
            move.a = target;
            move.b = shape[inst.a].w[1];
            move.vals = { bytes };
            EmitE(std::move(move));
            SimpleE(GirOp::StackRelease, shape[inst.a].w[0], PtrAt(target, bytes, 1));
            shape[inst.res].w[1] = target;
        }
        Event(GirEventKind::Relocate, { DestinationId(inst.a) }, inst.reason);
    }

    void LowerAppendValue(const GirInst &inst) {
        auto [base, old] = Sample(inst.a);
        (void)base;
        auto snapshot = HT(hvt[inst.b]);
        auto id = TraceId(GirTraceKind::Destination);
        Event(GirEventKind::Begin, { id });
        auto stack = shape[inst.a].w[1];
        auto start = Simple(GirOp::StackMark, Ptr(), stack);
        auto bytes = ConstI(I64(), Size(hvt[inst.b]));
        SimpleE(GirOp::StackBump, stack, bytes);
        CopyDynamic(start, shape[inst.b].w[0], bytes);
        ForCount(ConstI(I64(), snapshot.count), [&](int index) { Event(GirEventKind::Write, { id, index }); });
        SimpleE(GirOp::HdrSetLen, shape[inst.a].w[0], BinW(CoreBinOp::Add, I64(), old, ConstI(I64(), snapshot.count), true, inst.org));
        Event(GirEventKind::Publish, { id });
    }

    int CountMember() {
        GirMember member;
        member.kind = GirMember::Scalar;
        member.ty = I64();
        member.scope = 0;
        member.name = "render_count";
        auto index = Member(std::move(member));
        SimpleE(GirOp::LocalSet, ConstI(I64(), 0), -1, index);
        return index;
    }

    void RenderAppend(int stack, int countMember, int source, int count) {
        auto address = Simple(GirOp::StackMark, Ptr(), stack);
        SimpleE(GirOp::StackBump, stack, count);
        CopyDynamic(address, source, count);
        auto previous = Simple(GirOp::LocalGet, I64(), -1, -1, countMember);
        SimpleE(GirOp::LocalSet, BinW(CoreBinOp::Add, I64(), previous, count), -1, countMember);
    }

    void RenderText(int stack, int countMember, const string &text) {
        GirInst literal;
        literal.op = GirOp::StaticBytes;
        literal.bytes.assign(text.begin(), text.end());
        RenderAppend(stack, countMember, Emit(std::move(literal), Ptr()), ConstI(I64(), (int64_t)text.size()));
    }

    void RenderScalar(int stack, int countMember, GirTypeId type, int value) {
        auto buffer = Simple(GirOp::FrameAddr, Ptr(), -1, -1, FrameTemp(32));
        GirInst format;
        format.op = GirOp::Format;
        format.a = value;
        format.b = buffer;
        format.format = HT(type).kind == CoreType::Bool ? GirFormatKind::Bool :
                        CoreIsUnsigned(HT(type).ity) ? GirFormatKind::Uint : GirFormatKind::Int;
        RenderAppend(stack, countMember, buffer, Emit(std::move(format), I64()));
    }

    void RenderRun(int stack, int countMember, GirTypeId element, int base, int count, bool nested) {
        if (HT(element).kind == CoreType::Int && HT(element).ity == CoreIntTy::U8) {
            if (!nested) { RenderAppend(stack, countMember, base, count); return; }
            RenderText(stack, countMember, "\"");
            ForCount(count, [&](int index) {
                auto byte = PLoadV(l.IntType(CoreIntTy::U8), PtrAt(base, index, 1));
                vector<pair<int, string>> escapes = { { 34, "\\\"" }, { 92, "\\\\" }, { 10, "\\n" }, { 13, "\\r" }, { 9, "\\t" } };
                auto done = NewBlockL({});
                for (auto &[code, text] : escapes) {
                    auto hit = NewBlockL({});
                    auto next = NewBlockL({});
                    GirInst choose;
                    choose.op = GirOp::CondBr;
                    choose.a = CmpI(CoreCmpOp::Eq, l.IntType(CoreIntTy::U8), byte, ConstI(l.IntType(CoreIntTy::U8), code));
                    choose.idx = hit;
                    choose.idx2 = next;
                    Term(std::move(choose));
                    cur = hit;
                    RenderText(stack, countMember, text);
                    GirInst finish;
                    finish.op = GirOp::Br;
                    finish.idx = done;
                    Term(std::move(finish));
                    cur = next;
                }
                RenderAppend(stack, countMember, PtrAt(base, index, 1), ConstI(I64(), 1));
                GirInst finish;
                finish.op = GirOp::Br;
                finish.idx = done;
                Term(std::move(finish));
                cur = done;
            });
            RenderText(stack, countMember, "\"");
            return;
        }
        RenderText(stack, countMember, "[");
        ForCount(count, [&](int index) {
            auto separator = NewBlockL({});
            auto body = NewBlockL({});
            GirInst choose;
            choose.op = GirOp::CondBr;
            choose.a = CmpI(CoreCmpOp::Ne, I64(), index, ConstI(I64(), 0));
            choose.idx = separator;
            choose.idx2 = body;
            Term(std::move(choose));
            cur = separator;
            RenderText(stack, countMember, ", ");
            GirInst continueBody;
            continueBody.op = GirOp::Br;
            continueBody.idx = body;
            Term(std::move(continueBody));
            cur = body;
            RenderStored(stack, countMember, element, ElementAt(element, base, index), true);
        });
        RenderText(stack, countMember, "]");
    }

    void RenderStored(int stack, int countMember, GirTypeId type, int address, bool nested) {
        auto &value = HT(type);
        if (value.kind == CoreType::Int || value.kind == CoreType::Bool) {
            RenderScalar(stack, countMember, type, LoadScalarBytes(Words(type)[0], address));
            return;
        }
        if (value.kind == CoreType::Struct) {
            auto &descriptor = h.structs[value.structid];
            RenderText(stack, countMember, descriptor.displayName + " { ");
            for (size_t field = 0; field < descriptor.fields.size(); field++) {
                if (field) RenderText(stack, countMember, ", ");
                auto &part = descriptor.fields[field];
                RenderStored(stack, countMember, part.type, PtrAt(address, ConstI(I64(), part.offset), 1), true);
            }
            RenderText(stack, countMember, " }");
            return;
        }
        auto base = address;
        auto count = ConstI(I64(), value.count);
        if (value.kind == CoreType::VarArr) {
            base = PtrAt(address, ConstI(I64(), 4), 1);
            count = Conv(LoadScalarBytes(l.IntType(CoreIntTy::U32), address), l.IntType(CoreIntTy::U32), I64());
        }
        RenderRun(stack, countMember, value.elem, base, count, nested);
    }

    void RenderOperand(int value, int stack, int countMember) {
        auto &type = HT(hvt[value]);
        if (type.kind == CoreType::Unit) {
            RenderText(stack, countMember, "()");
        } else if (type.kind == CoreType::Int || type.kind == CoreType::Bool) {
            RenderScalar(stack, countMember, hvt[value], shape[value].w[0]);
        } else if (type.kind == CoreType::View || type.kind == CoreType::Slice) {
            auto [base, count] = Sample(value);
            RenderRun(stack, countMember, type.elem, base, count, false);
        } else RenderStored(stack, countMember, hvt[value], shape[value].w[0], false);
    }

    void LowerRender(const GirInst &inst) {
        auto stack = StackOf(scratchStacks.at(inst.res));
        auto start = Simple(GirOp::StackMark, Ptr(), stack);
        auto count = CountMember();
        RenderOperand(inst.a, stack, count);
        Define(inst, { start, Simple(GirOp::LocalGet, I64(), -1, -1, count) });
    }

    void TextDestination(const GirInst &inst) {
        auto stack = shape[inst.a].w[0];
        auto start = Simple(GirOp::StackMark, Ptr(), stack);
        auto countMember = CountMember();
        RenderOperand(inst.b, stack, countMember);
        auto count = Simple(GirOp::LocalGet, I64(), -1, -1, countMember);
        auto old = DestinationCount(inst.a);
        ForCount(count, [&](int index) {
            Event(GirEventKind::Write, { DestinationId(inst.a), BinW(CoreBinOp::Add, I64(), old, index) });
        });
        PStoreV(I64(), shape[inst.a].w[2], BinW(CoreBinOp::Add, I64(), old, count));
        (void)start;
        if (scratchStacks.count(inst.b))
            SimpleE(GirOp::StackRelease, StackOf(scratchStacks.at(inst.b)), shape[inst.b].w[0]);
    }

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
                if (CoreHasConstruction(h.profile)) shape[i.res].source = ChildSource(shape[i.a].source, idx);
                Define(i, { CoreHasConstruction(h.profile) ? ElementAt(HT(hvt[i.a]).elem, shape[i.a].w[0], idx) : PtrAt(shape[i.a].w[0], idx, esz) });
                return;
            }
            case GirOp::Field: {
                auto ref = hvt[i.a];
                auto owner = HT(ref).elem;
                auto sid = HT(owner).structid;
                auto offset = h.structs.at(sid).fields.at(i.idx).offset;
                Define(i, { PtrAt(shape[i.a].w[0], ConstI(I64(), offset), 1) });
                shape[i.res].unaligned = true;
                if (CoreHasConstruction(h.profile)) shape[i.res].source = ChildSource(shape[i.a].source, ConstI(I64(), i.idx));
                return;
            }
            case GirOp::DestOpen: return Open(i);
            case GirOp::DestChild: {
                Destination child;
                child.stack = shape[i.a].w[0];
                child.base = Simple(GirOp::StackMark, Ptr(), child.stack);
                child.metadata = Metadata(TraceId(GirTraceKind::Destination));
                child.type = i.ty;
                destinations[carrierRoots[i.res]] = child;
                Define(i, { child.stack, child.base, child.metadata });
                Event(GirEventKind::Begin, { DestinationId(i.res) });
                StartPrefix(i.res);
                return;
            }
            case GirOp::DestBytes:
                for (auto byte : i.bytes) WriteFixed(i.a, HT(HT(hvt[i.a]).elem).elem,
                                                    { ConstI(l.IntType(CoreIntTy::U8), byte) });
                return;
            case GirOp::DestWrite: WriteFixed(i.a, HT(HT(hvt[i.a]).elem).elem, shape[i.b].w); return;
            case GirOp::DestSnapshot: {
                auto &snapshot = HT(hvt[i.b]);
                for (int64_t index = 0; index < snapshot.count; index++) {
                    auto source = PtrAt(shape[i.b].w[0], ConstI(I64(), index), Size(snapshot.elem));
                    vector<int> value = IsAggregate(snapshot.elem) ? vector<int> { source } :
                                       vector<int> { LoadScalarBytes(Words(snapshot.elem)[0], source) };
                    WriteFixed(i.a, snapshot.elem, value);
                }
                return;
            }
            case GirOp::DestCopy: return CopyDestination(i);
            case GirOp::DestRepeat: return RepeatDestination(i);
            case GirOp::DestAttach: IncrementDestination(i.a); return;
            case GirOp::DestFinish: {
                PatchPrefix(i.a, i.org);
                shape[i.res] = shape[i.a];
                return;
            }
            case GirOp::DestPublish: Publish(i.a, i.org); return;
            case GirOp::DestPublishRef: {
                auto destination = DestinationAt(i.a);
                Publish(i.a, i.org);
                Define(i, { shape[i.a].w[1] });
                shape[i.res].source = ChildSource(shape[destination.receiverReference].source, destination.oldLength);
                return;
            }
            case GirOp::DestArg: {
                auto destination = DestinationAt(i.a);
                Publish(i.a, i.org);
                shape[i.res].source = destination.source;
                ownedArguments[i.res] = { shape[i.a].w[0], shape[i.a].w[1] };
                if (IsResizableKind(HT(destination.type).kind)) {
                    auto header = Simple(GirOp::FrameAddr, Ptr(), -1, -1, FrameTemp(16));
                    SimpleE(GirOp::HdrInit, header, shape[i.a].w[1]);
                    SimpleE(GirOp::HdrSetLen, header, DestinationCount(i.a));
                    Define(i, { header, shape[i.a].w[0] });
                } else Define(i, { shape[i.a].w[1], shape[i.a].w[0] });
                return;
            }
            case GirOp::DestBind: {
                auto destination = DestinationAt(i.a);
                CreateObject(i.idx);
                namedDestinations[i.idx] = destination;
                auto &place = places[i.idx];
                if (place.kind != Place::Alias) throw CompileError { "named result has no alias placement" };
                auto reference = shape[i.a].w[1];
                if (IsResizableKind(HT(hf->slots[i.idx].ty).kind)) {
                    reference = Simple(GirOp::FrameAddr, Ptr(), -1, -1, FrameTemp(16));
                    auto prefix = Prefix(HT(hvt[i.a]).elem, HT(hvt[i.a]).request);
                    auto elements = prefix ? PtrAt(shape[i.a].w[1], ConstI(I64(), prefix), 1) : shape[i.a].w[1];
                    SimpleE(GirOp::HdrInit, reference, elements);
                    SimpleE(GirOp::HdrSetLen, reference, DestinationCount(i.a));
                }
                SimpleE(GirOp::LocalSet, reference, -1, place.members[0]);
                SimpleE(GirOp::LocalSet, destination.stack, -1, place.members[1]);
                return;
            }
            case GirOp::DestNamed: {
                auto destination = namedDestinations.at(i.idx);
                destinations[carrierRoots[i.res]] = destination;
                if (IsResizableKind(HT(hf->slots[i.idx].ty).kind)) {
                    auto header = Simple(GirOp::LocalGet, Ptr(), -1, -1, places[i.idx].members[0]);
                    PStoreV(I64(), destination.metadata, Simple(GirOp::HdrLen, I64(), header));
                }
                Define(i, { destination.stack, destination.base, destination.metadata });
                PatchPrefix(i.res, i.org);
                return;
            }
            case GirOp::DestAbandon: {
                Event(GirEventKind::Abandon, { DestinationId(i.a) });
                shape[i.res] = shape[i.a];
                return;
            }
            case GirOp::DestCancel:
                if (!shape[i.a].w.empty()) ReleaseUnprotected(shape[i.a].w[0], shape[i.a].w[1]);
                return;
            case GirOp::DestValue: case GirOp::DestRelocate: case GirOp::DestStage: case GirOp::DestFit:
            case GirOp::DestAdapt: case GirOp::DestAdaptFinish:
                return AdaptDestination(i);
            case GirOp::ResultExitDest: {
                auto outputs = resultOutputs.at(i.idx);
                Destination destination;
                destination.stack = outputs[0];
                destination.base = Simple(GirOp::StackMark, Ptr(), destination.stack);
                destination.metadata = outputs[2];
                PStoreV(I64(), destination.metadata, ConstI(I64(), 0));
                destination.type = i.ty;
                destination.request = i.request;
                destination.resultPosition = i.idx;
                destinations[carrierRoots[i.res]] = destination;
                Define(i, { destination.stack, destination.base, destination.metadata });
                StartPrefix(i.res);
                return;
            }
            case GirOp::TargetDest: {
                auto &channel = l.lowtargets[i.idx].channels[i.idx2];
                Destination destination;
                destination.stack = TargetCell(i.idx, channel.incoming[0]);
                destination.base = Simple(GirOp::StackMark, Ptr(), destination.stack);
                destination.metadata = TargetCell(i.idx, channel.incoming[2]);
                destination.type = i.ty;
                destination.request = i.request;
                destination.resultPosition = i.idx2;
                destination.target = i.idx;
                PStoreV(I64(), destination.metadata, ConstI(I64(), 0));
                destinations[carrierRoots[i.res]] = destination;
                Define(i, { destination.stack, destination.base, destination.metadata });
                StartPrefix(i.res);
                return;
            }
            case GirOp::DestAbandonNamed: {
                auto destination = namedDestinations.at(i.idx);
                Event(GirEventKind::Abandon, { PLoadV(I64(), WordAt(destination.metadata, 1)) });
                Define(i, {});
                namedDestinations.erase(i.idx);
                return;
            }
            case GirOp::Bytes: {
                GirInst bytes;
                bytes.op = GirOp::StaticBytes;
                bytes.bytes = i.bytes;
                Define(i, { Emit(std::move(bytes), Ptr()), ConstI(I64(), (int64_t)i.bytes.size()) });
                return;
            }
            case GirOp::Render: return LowerRender(i);
            case GirOp::DestText: return TextDestination(i);
            case GirOp::CallConstruct: return LowerCall(i);
            case GirOp::AppendValue: return LowerAppendValue(i);
            case GirOp::Freeze: shape[i.res] = shape[i.a]; return;
            case GirOp::Load: return LowerLoad(i);
            case GirOp::Snap: return LowerSnap(i);
            case GirOp::SliceView: shape[i.res] = shape[i.a]; return;
            case GirOp::ViewLen: Define(i, { shape[i.a].w[1] }); return;
            case GirOp::ViewSlice: return LowerViewSlice(i);
            case GirOp::ArrayLen: {
                if (CoreHasConstruction(h.profile)) { Define(i, { Sample(i.a).second }); return; }
                auto &pt = HT(HT(hvt[i.a]).elem);
                if (pt.kind == CoreType::Arr) Define(i, { ConstI(I64(), pt.count) });
                else if (pt.kind == CoreType::Limited)
                    Define(i, { LimitedLength(shape[i.a].w[0], HT(hvt[i.a]).elem) });
                else Define(i, { Simple(GirOp::HdrLen, I64(), shape[i.a].w[0]) });
                return;
            }
            case GirOp::Index: return LowerIndex(i);
            case GirOp::IndexProven: return LowerIndexProven(i);
            case GirOp::Push: return LowerPush(i);
            case GirOp::Pop: return LowerPop(i);
            case GirOp::Call: return LowerCall(i);
            case GirOp::Invoke: return LowerCall(i);
            case GirOp::Escape: return LowerEscape(i);
            case GirOp::Result: {
                auto &parts = HT(hvt[i.a]).parts;
                size_t offset = 0;
                for (int part = 0; part < i.idx; part++) offset += Words(parts[part]).size();
                auto count = Words(parts[i.idx]).size();
                if (callResultSources.count(i.a)) shape[i.res].source = callResultSources.at(i.a)[i.idx];
                Define(i, vector<int>(shape[i.a].w.begin() + offset, shape[i.a].w.begin() + offset + count));
                return;
            }
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
            default: throw GirLowerUnsupported { "construction-operation", hf->name, i.org };
        }
    }

    int ToI64(int hv) {
        auto &c = HT(hvt[hv]);
        return Conv(shape[hv].w[0], l.IntType(c.ity), I64());
    }

    void LowerSlot(const GirInst &i) {
        if (CoreHasConstruction(h.profile)) shape[i.res].source = Simple(GirOp::LocalGet, Ptr(), -1, -1, sourceMembers[i.idx]);
        auto &p = places[i.idx];
        switch (p.kind) {
            case Place::Alias:
                for (auto member : p.members) shape[i.res].w.push_back(Simple(GirOp::LocalGet, Ptr(), -1, -1, member));
                return;
            case Place::Dynamic: Define(i, { Simple(GirOp::LocalGet, Ptr(), -1, -1, p.members[0]) }); return;
            case Place::Words: shape[i.res].slot = i.idx; return;
            case Place::Header: {
                if (namedDestinations.count(i.idx)) {
                    auto destination = namedDestinations.at(i.idx);
                    auto hdr = Simple(GirOp::FrameAddr, Ptr(), -1, -1, p.members[0]);
                    Define(i, { hdr, destination.stack });
                    return;
                }
                auto hdr = Simple(GirOp::FrameAddr, Ptr(), -1, -1, p.members[0]);
                Define(i, { hdr, StackOf(p.stack) });
                return;
            }
            default: Define(i, { Simple(GirOp::FrameAddr, Ptr(), -1, -1, p.members[0]) }); return;
        }
    }

    void LowerGlobalAddr(const GirInst &i) {
        auto &g = l.lowglobals[i.idx];
        if (CoreHasConstruction(h.profile)) shape[i.res].source = Simple(GirOp::SourceGlobal, Ptr(), -1, -1, i.idx);
        auto addr = Simple(GirOp::GlobalAddr, Ptr(), -1, -1, i.idx);
        if (g.kind == GirMember::Header) Define(i, { addr, Simple(GirOp::GlobalStack, Ptr(), -1, -1, i.idx) });
        else if (g.kind == GirMember::Dynamic) Define(i, { PLoadV(Ptr(), addr) });
        else Define(i, { addr });
    }

    void LowerLoad(const GirInst &i) {
        auto &rs = shape[i.a];
        auto t = hvt[i.res];
        shape[i.res].source = rs.source;
        if (CoreHasConstruction(h.profile) && rs.slot >= 0 && HT(t).kind == CoreType::Ref)
            shape[i.res].source = Simple(GirOp::LocalGet, Ptr(), -1, -1, referenceSources[rs.slot]);
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
        shape[i.res].source = shape[i.a].source;
        if (CoreHasConstruction(h.profile)) {
            auto [base, count] = Sample(i.a);
            Define(i, { base, count });
            return;
        }
        auto owner = HT(hvt[i.a]).elem;
        auto &pt = HT(owner);
        auto r = shape[i.a].w[0];
        if (pt.kind == CoreType::Arr) Define(i, { r, ConstI(I64(), pt.count) });
        else if (pt.kind == CoreType::Limited)
            Define(i, { LimitedData(r, owner), LimitedLength(r, owner) });
        else Define(i, { Simple(GirOp::HdrBase, Ptr(), r), Simple(GirOp::HdrLen, I64(), r) });
    }

    void LowerViewSlice(const GirInst &i) {
        shape[i.res].source = shape[i.a].source;
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
        auto data = CoreHasConstruction(h.profile) ? ElementAt(HT(hvt[i.res]).elem, base, lo) : PtrAt(base, lo, esz);
        auto len = BinW(CoreBinOp::Sub, I64(), hi, lo);
        Define(i, { data, len });
    }

    void LowerIndex(const GirInst &i) {
        auto esz = Size(HT(hvt[i.res]).elem);
        auto base = shape[i.a].w[0], n = shape[i.a].w[1];
        auto idx = ToI64(i.b);
        auto fail = AbortBlock(GirAbortKind::IndexOob, { idx, n }, i.org);
        CheckThen(CmpI(CoreCmpOp::Lt, U64(), Conv(idx, I64(), U64()), Conv(n, I64(), U64())), fail);
        if (CoreHasConstruction(h.profile)) shape[i.res].source = ChildSource(shape[i.a].source, idx);
        Define(i, { CoreHasConstruction(h.profile) ? ElementAt(HT(hvt[i.res]).elem, base, idx) : PtrAt(base, idx, esz) });
    }

    void LowerIndexProven(const GirInst &i) {
        auto esz = Size(HT(hvt[i.res]).elem);
        auto base = shape[i.a].w[0];
        auto idx = ToI64(i.b);
        if (CoreHasConstruction(h.profile)) shape[i.res].source = ChildSource(shape[i.a].source, idx);
        Define(i, { CoreHasConstruction(h.profile) ? ElementAt(HT(hvt[i.res]).elem, base, idx) : PtrAt(base, idx, esz) });
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
        else if (CoreHasShrink(h.profile))
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
        auto destination = CoreHasConstruction(h.profile) ? TraceId(GirTraceKind::Destination) : -1;
        if (destination >= 0) Event(GirEventKind::Begin, { destination });
        auto base = OwnerData(i.a, owner);
        auto at = PtrAt(base, len, esz);
        StoreAt(elemty, at, shape[i.b].w);
        if (destination >= 0) Event(GirEventKind::Write, { destination, ConstI(I64(), 0) });
        // Pilot push has no source-origin requirement, so keep its length increment unchecked.
        auto newLen = CoreHasShrink(h.profile)
            ? BinW(CoreBinOp::Add, I64(), len, ConstI(I64(), 1), true, i.org)
            : BinW(CoreBinOp::Add, I64(), len, ConstI(I64(), 1));
        if (limited) SetLimitedLength(address, owner, newLen);
        else {
            SimpleE(GirOp::StackBump, rs.w[1], -1, (int)esz);
            SimpleE(GirOp::HdrSetLen, address, newLen);
        }
        if (destination >= 0) Event(GirEventKind::Publish, { destination });
        Define(i, { at });
        if (CoreHasConstruction(h.profile)) shape[i.res].source = ChildSource(rs.source, len);
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
            if (CoreHasShrink(h.profile)) StoreScalarBytes(Words(c.elem)[0], src, w[0]);
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
        if (p.kind == Place::Alias) {
            SimpleE(GirOp::LocalSet, shape[i.a].source, -1, sourceMembers[i.idx]);
            for (size_t word = 0; word < p.members.size(); word++)
                SimpleE(GirOp::LocalSet, shape[i.a].w[word], -1, p.members[word]);
            return;
        }
        if (CoreHasConstruction(h.profile)) {
            CreateObject(i.idx);
            if (HT(hf->slots[i.idx].ty).kind == CoreType::Ref && shape[i.a].source >= 0)
                SimpleE(GirOp::LocalSet, shape[i.a].source, -1, referenceSources[i.idx]);
        }
        auto t = hf->slots[i.idx].ty;
        auto &v = shape[i.a];
        switch (p.kind) {
            case Place::Dynamic: case Place::Alias:
                throw CompileError { "nonfixed initialization requires a construction or owned-parameter alias" };
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
            if (CoreHasConstruction(h.profile) && HT(hvt[i.b]).kind == CoreType::Ref)
                SimpleE(GirOp::LocalSet, shape[i.b].source, -1, referenceSources[rs.slot]);
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
            ReleaseUnprotected(StackOf(places[hs[k - 1]].stack), it->second[k - 1]);
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
        if (CoreHasConstruction(h.profile)) {
            auto count = ConstI(I64(), 1);
            vector<pair<int, int>> runs;
            for (auto &part : i.parts) {
                if (part.text) {
                    GirInst literal;
                    literal.op = GirOp::StaticBytes;
                    literal.bytes.assign(part.str.begin(), part.str.end());
                    runs.push_back({ Emit(std::move(literal), Ptr()), ConstI(I64(), (int64_t)part.str.size()) });
                } else if (HT(hvt[part.val]).kind == CoreType::View) runs.push_back({ shape[part.val].w[0], shape[part.val].w[1] });
                else {
                    auto buffer = Simple(GirOp::FrameAddr, Ptr(), -1, -1, FrameTemp(32));
                    GirInst format;
                    format.op = GirOp::Format;
                    auto &type = HT(hvt[part.val]);
                    format.format = type.kind == CoreType::Bool ? GirFormatKind::Bool :
                                    CoreIsUnsigned(type.ity) ? GirFormatKind::Uint : GirFormatKind::Int;
                    format.a = shape[part.val].w[0];
                    format.b = buffer;
                    runs.push_back({ buffer, Emit(std::move(format), I64()) });
                }
                count = BinW(CoreBinOp::Add, I64(), count, runs.back().second, true, i.org);
            }
            CheckThen(CmpI(CoreCmpOp::Ge, I64(), count, ConstI(I64(), 0)), AbortBlock(GirAbortKind::Capacity, {}, i.org));
            auto stack = StackOf(printStacks.at(&i));
            auto base = Simple(GirOp::StackMark, Ptr(), stack);
            SimpleE(GirOp::StackBump, stack, count);
            auto offset = ConstI(I64(), 0);
            for (auto [source, length] : runs) {
                CopyDynamic(PtrAt(base, offset, 1), source, length);
                offset = BinW(CoreBinOp::Add, I64(), offset, length);
            }
            PStoreV(l.IntType(CoreIntTy::U8), PtrAt(base, offset, 1), ConstI(l.IntType(CoreIntTy::U8), 10));
            GirInst output;
            output.op = GirOp::OutBytes;
            output.a = base;
            output.b = count;
            output.org = i.org;
            EmitE(std::move(output));
            SimpleE(GirOp::StackRelease, stack, base);
            for (auto &part : i.parts)
                if (!part.text && scratchStacks.count(part.val))
                    SimpleE(GirOp::StackRelease, StackOf(scratchStacks.at(part.val)), shape[part.val].w[0]);
            return;
        }
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
        c.vals.push_back(lf.stacks ? BinW(CoreBinOp::Add, I64(), spval, ConstI(I64(), lf.stacks), CoreHasConstruction(h.profile), i.org) : spval);
        if (CoreHasConstruction(h.profile)) {
            for (size_t parameter = 0; parameter < i.vals.size(); parameter++) {
                auto argument = i.vals[parameter];
                auto count = GirNonfixed(h, g.params[parameter]) ? 2 : (int)Words(g.params[parameter]).size();
                if ((int)shape[argument].w.size() < count) throw CompileError { "call argument omits an ABI word" };
                for (int word = 0; word < count; word++) c.vals.push_back(shape[argument].w[word]);
            }
            vector<vector<int>> addresses;
            size_t channel = 0;
            for (size_t result = 0; result < g.results.size(); result++) {
                vector<int> cells;
                if (GirNonfixed(h, g.results[result])) cells = shape[i.vals2[channel++]].w;
                else for (auto wordType : s.resultWords[result]) {
                    auto size = IsAggregate(g.results[result]) ? Size(g.results[result]) : 8;
                    auto pointer = Simple(GirOp::FrameAddr, Ptr(), -1, -1, FrameTemp(size));
                    cells.push_back(pointer);
                    (void)wordType;
                }
                for (auto cell : cells) c.vals.push_back(cell);
                addresses.push_back(std::move(cells));
            }
            GirInst shadow;
            shadow.op = GirOp::SourceCallPush;
            shadow.vals.assign(c.vals.size() - 1, -1);
            size_t primitive = 1;
            for (size_t parameter = 0; parameter < i.vals.size(); parameter++) {
                auto type = g.params[parameter];
                if (HT(type).kind == CoreType::Ref || GirNonfixed(h, type)) {
                    auto source = shape[i.vals[parameter]].source;
                    if (source < 0) throw CompileError { "borrowed call argument omits its source metadata" };
                    shadow.vals[primitive - 1] = source;
                }
                primitive += GirNonfixed(h, type) ? 2 : Words(type).size();
            }
            auto token = Emit(std::move(shadow), Ptr());
            EmitE(std::move(c));
            if (i.op == GirOp::Invoke) {
                auto flag = Simple(GirOp::ReturnFlagGet, I64());
                auto normal = NewBlockL({});
                auto escape = NewBlockL({});
                GirInst dispatch;
                dispatch.op = GirOp::CondBr;
                dispatch.a = CmpI(CoreCmpOp::Eq, I64(), flag, ConstI(I64(), 0));
                dispatch.idx = normal;
                dispatch.idx2 = escape;
                Term(std::move(dispatch));
                cur = escape;
                for (auto &edge : i.escapes) {
                    auto hit = NewBlockL({});
                    auto next = NewBlockL({});
                    dispatch = GirInst {};
                    dispatch.op = GirOp::CondBr;
                    dispatch.a = CmpI(CoreCmpOp::Eq, I64(), flag, ConstI(I64(), edge.target + 1));
                    dispatch.idx = hit;
                    dispatch.idx2 = next;
                    Term(std::move(dispatch));
                    cur = hit;
                    vector<Shape> produced;
                    auto &target = l.lowtargets[edge.target];
                    auto &results = h.funcs[h.targets[edge.target].members[0]].results;
                    for (size_t result = 0; result < results.size(); result++) {
                        auto &channel = target.channels[result];
                        Shape payload;
                        if (GirNonfixed(h, results[result])) {
                            auto stack = TargetCell(edge.target, channel.incoming[0]);
                            auto start = TargetCell(edge.target, channel.escaped[0]);
                            auto metadata = TargetCell(edge.target, channel.incoming[2]);
                            PStoreV(I64(), metadata, TargetCell(edge.target, channel.escaped[2]));
                            payload.w = { stack, start, metadata };
                            auto parameter = hf->blocks[edge.block].params[result].first;
                            Destination destination;
                            destination.stack = stack;
                            destination.base = start;
                            destination.metadata = metadata;
                            destination.type = results[result];
                            destination.request = h.funcs[h.targets[edge.target].members[0]].resultProtocols[result].request;
                            destination.resultPosition = (int)result;
                            destination.target = edge.target;
                            auto root = carrierRoots[parameter];
                            auto endMember = payloadEndMembers.find(root);
                            if (endMember == payloadEndMembers.end()) {
                                GirMember member;
                                member.kind = GirMember::Scalar;
                                member.ty = Ptr();
                                member.scope = 0;
                                member.name = "escaped_payload_end";
                                endMember = payloadEndMembers.emplace(root, Member(std::move(member))).first;
                            }
                            destination.payloadEndMember = endMember->second;
                            SimpleE(GirOp::LocalSet, TargetCell(edge.target, channel.escaped[1]), -1, destination.payloadEndMember);
                            destinations[root] = destination;
                        } else {
                            for (auto cell : channel.escaped) payload.w.push_back(TargetCell(edge.target, cell));
                            if (HT(results[result]).kind == CoreType::Ref && HandlesTarget(edge.target))
                                payload.source = Simple(GirOp::SourceTargetGet, Ptr(), targetTokens.at(edge.target), -1, (int)result);
                        }
                        produced.push_back(std::move(payload));
                    }
                    for (auto value : i.vals2) produced.push_back(shape[value]);
                    SimpleE(GirOp::SourceCallPop, token);
                    auto previousProtection = protectedStacks;
                    for (size_t result = 0; result < results.size(); result++)
                        if (GirNonfixed(h, results[result])) protectedStacks.push_back(produced[result].w[0]);
                    for (auto argument : i.vals) if (ownedArguments.count(argument)) {
                        auto [stack, start] = ownedArguments.at(argument);
                        ReleaseUnprotected(stack, start);
                    }
                    BranchProduced(edge.block, produced, edge.forwarded);
                    protectedStacks = std::move(previousProtection);
                    cur = next;
                }
                GirInst invalid;
                invalid.op = GirOp::Unreachable;
                Term(std::move(invalid));
                cur = normal;
            }
            vector<int> resultSources(g.results.size(), -1);
            for (size_t result = 0; result < g.results.size(); result++) {
                if (HT(g.results[result]).kind == CoreType::Ref)
                    resultSources[result] = Simple(GirOp::SourceCallGet, Ptr(), token, -1, (int)primitive);
                primitive += s.resultWords[result].size();
            }
            SimpleE(GirOp::SourceCallPop, token);
            if (i.op != GirOp::Invoke) {
                if (g.results.size() == 1) shape[i.res].source = resultSources[0];
                else callResultSources[i.res] = resultSources;
            }
            vector<int> results;
            for (size_t result = 0; result < g.results.size(); result++)
                for (size_t word = 0; word < s.resultWords[result].size(); word++)
                    results.push_back(GirNonfixed(h, g.results[result]) || IsAggregate(g.results[result]) ? addresses[result][word] :
                                      PLoadV(s.resultWords[result][word], addresses[result][word]));
            if (i.op == GirOp::Invoke) {
                vector<Shape> produced;
                size_t offset = 0;
                for (size_t result = 0; result < g.results.size(); result++) {
                    Shape value;
                    auto count = s.resultWords[result].size();
                    value.w.assign(results.begin() + offset, results.begin() + offset + count);
                    value.source = resultSources[result];
                    produced.push_back(std::move(value));
                    offset += count;
                }
                for (auto argument : i.vals) if (ownedArguments.count(argument)) {
                    auto [stack, start] = ownedArguments.at(argument);
                    ReleaseUnprotected(stack, start);
                }
                BranchProduced(i.a, produced, i.forwarded);
            } else Define(i, std::move(results));
            for (auto argument : i.vals) if (ownedArguments.count(argument)) {
                auto [stack, start] = ownedArguments.at(argument);
                SimpleE(GirOp::StackRelease, stack, start);
                ownedArguments.erase(argument);
            }
            return;
        }
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
        if (CoreHasConstruction(h.profile)) {
            for (size_t result = 0; result < i.vals.size(); result++) {
                auto &value = shape[i.vals[result]];
                auto type = hf->results[result];
                if (GirNonfixed(h, type)) {
                    PStoreV(I64(), resultOutputs[result][2], DestinationCount(i.vals[result]));
                } else if (IsAggregate(type)) Copy(resultOutputs[result][0], value.w[0], Size(type));
                else {
                    auto words = Words(type);
                    for (size_t word = 0; word < words.size(); word++)
                        PStoreV(words[word], resultOutputs[result][word], value.w[word]);
                }
            }
            for (size_t result = 0; result < i.vals.size(); result++) {
                auto value = i.vals[result];
                if ((HT(hf->results[result]).kind == CoreType::Ref) && shape[value].source >= 0)
                    SimpleE(GirOp::SourceResult, shape[value].source, -1, resultOutputPositions[result][0]);
            }
            LeaveTargets();
            SimpleE(GirOp::ReturnFlagSet, ConstI(I64(), 0));
            SimpleE(GirOp::SourceLeave, sourceScope);
            GirInst ret;
            ret.op = GirOp::Ret;
            ret.org = i.org;
            Term(std::move(ret));
            return;
        }
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

    void LowerEscape(const GirInst &i) {
        auto &results = h.funcs[h.targets[i.idx].members[0]].results;
        auto &table = l.lowtargets[i.idx];
        auto previousProtection = protectedStacks;
        for (size_t result = 0; result < results.size(); result++)
            if (GirNonfixed(h, results[result])) protectedStacks.push_back(shape[i.vals[result]].w[0]);
        for (auto cancelled : i.vals2)
            if (!shape[cancelled].w.empty()) ReleaseUnprotected(shape[cancelled].w[0], shape[cancelled].w[1]);
        for (size_t result = 0; result < results.size(); result++) {
            auto value = i.vals[result];
            auto &channel = table.channels[result];
            if (GirNonfixed(h, results[result])) {
                SetTargetCell(i.idx, channel.escaped[0], shape[value].w[1]);
                SetTargetCell(i.idx, channel.escaped[1], Simple(GirOp::StackMark, Ptr(), shape[value].w[0]));
                SetTargetCell(i.idx, channel.escaped[2], DestinationCount(value));
            } else if (IsAggregate(results[result])) {
                auto destination = TargetCell(i.idx, channel.incoming[0]);
                Copy(destination, shape[value].w[0], Size(results[result]));
                SetTargetCell(i.idx, channel.escaped[0], destination);
            } else {
                for (size_t word = 0; word < channel.escaped.size(); word++) SetTargetCell(i.idx, channel.escaped[word], shape[value].w[word]);
                if (HT(results[result]).kind == CoreType::Ref && shape[value].source >= 0) {
                    GirInst source;
                    source.op = GirOp::SourceTargetResult;
                    source.a = shape[value].source;
                    source.idx = i.idx;
                    source.idx2 = (int)result;
                    EmitE(std::move(source));
                }
            }
        }
        LeaveTargets();
        SimpleE(GirOp::ReturnFlagSet, ConstI(I64(), i.idx + 1));
        SimpleE(GirOp::SourceLeave, sourceScope);
        GirInst ret;
        ret.op = GirOp::Ret;
        ret.org = i.org;
        Term(std::move(ret));
        protectedStacks = std::move(previousProtection);
    }

    // A global's initializer writes the value into the global's storage.
    void LowerGlobalRet(const GirInst &i) {
        auto &g = h.globals[initglobal];
        if (CoreHasConstruction(h.profile) && GirNonfixed(h, g.ty)) {
            Publish(i.vals[0], i.org);
            SimpleE(GirOp::ReturnFlagSet, ConstI(I64(), 0));
            SimpleE(GirOp::SourceLeave, sourceScope);
            GirInst ret; ret.op = GirOp::Ret; Term(std::move(ret)); return;
        }
        if (CoreHasConstruction(h.profile)) {
            auto source = NewSource(TraceId(GirTraceKind::Storage));
            if (HT(g.ty).kind == CoreType::Ref && shape[i.vals[0]].source >= 0) source = shape[i.vals[0]].source;
            SimpleE(GirOp::SourceGlobalSet, source, -1, initglobal);
        }
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
        if (CoreHasConstruction(h.profile)) {
            SimpleE(GirOp::ReturnFlagSet, ConstI(I64(), 0));
            SimpleE(GirOp::SourceLeave, sourceScope);
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
                if (cycle && l.funcs[m].stacks > 0 && !CoreHasConstruction(h.profile))
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
