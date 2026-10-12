// Goose compiler — GIR-H, the in-memory module.
//
// GIR-H is a typed control-flow graph over scalar SSA values and memory slots.
// Data types are Core's, and a sampled view of a run of elements is one more
// type that exists only as an SSA value; both live in one type table
// (core_ir.h's CoreType, whose View kind is used only here). Slots, scopes and
// globals have the numbers of the Core variables, blocks and globals they came
// from. Value ids are dense within a function and each is defined once, in no
// particular order.
#pragma once

namespace goose {

using GirTypeId = CoreTypeId;

enum class GirOp : uint8_t {
    // Instructions that define a value, high stage.
    Int, Bool, Unit, Bin, Un, Cmp, BoolCmp, Not, Conv, Next, Slot, Global, Elem, Freeze, Load,
    Snap, SliceView, ViewLen, ViewSlice, ArrayLen, Index, Push, Call, Arr, Fill,
    // Instructions that define a value, low stage.
    PtrOffset, PLoad, FrameAddr, LocalGet, StackAt, StackMark, GlobalAddr, GlobalStack, HdrBase,
    HdrLen,
    // Instructions that define none, high stage.
    Init, Store, Append, Enter, Leave, Print,
    // Instructions that define none, low stage.
    PStore, LocalSet, StackRelease, StackBump, HdrInit, HdrSetLen, BytesCopy, BytesMove,
    BytesFill, RtCall,
    // Terminators.
    Br, CondBr, Ret, Abort, Exit,
};

inline bool GirDefines(GirOp op) { return op <= GirOp::HdrLen; }
inline bool GirIsTerminator(GirOp op) { return op >= GirOp::Br; }

// Whether an instruction belongs to the high stage only, the low stage only,
// or both (scalar arithmetic, calls and control flow).
inline bool GirHighOnly(GirOp op) {
    switch (op) {
        case GirOp::BoolCmp: case GirOp::Next: case GirOp::Slot: case GirOp::Global: case GirOp::Elem:
        case GirOp::Freeze: case GirOp::Load: case GirOp::Snap: case GirOp::SliceView:
        case GirOp::ViewLen: case GirOp::ViewSlice: case GirOp::ArrayLen: case GirOp::Index:
        case GirOp::Push: case GirOp::Arr: case GirOp::Fill: case GirOp::Unit: case GirOp::Init:
        case GirOp::Store: case GirOp::Append: case GirOp::Enter: case GirOp::Leave: case GirOp::Print:
            return true;
        default: return false;
    }
}
inline bool GirLowOnly(GirOp op) {
    return (op >= GirOp::PtrOffset && op <= GirOp::HdrLen) ||
           (op >= GirOp::PStore && op <= GirOp::RtCall);
}

enum class GirAbortKind : uint8_t {
    DivZero, DivOverflow, IndexOob, SliceOob, Assert, UserAbort, IntOverflow, CastRange,
};

inline const char *GirAbortKindName(GirAbortKind k) {
    static const char *names[] = { "div_zero", "div_overflow", "index_oob", "slice_oob", "assert",
                                   "user_abort", "int_overflow", "cast_range" };
    return names[(int)k];
}

// A bound of a slice operation: omitted, a value, or the length minus a value.
struct GirBound {
    enum Kind : uint8_t { None, Val, End } kind = None;
    int val = 0;
};

struct GirPart {
    bool text = false;
    string str;
    int val = 0;
};

// One instruction. `org` is an origin number of the module's origin table, or
// -1 for none. Which members an instruction reads is fixed by `op`:
//   Int: res, ty, text            Bool: res, flag             Unit: res
//   Bin: res, bin, ty, a, b, org  Un: res, un, ty, a, org     Cmp: res, cmp, ty, a, b
//   BoolCmp: res, cmp, a, b       Not: res, a
//   Conv: res, conv, ty (source), ty2 (target), a, org        Next: res, ty, a
//   Slot: res, idx (slot)         Global: res, idx (global)
//   Elem: res, a (view), b (index)
//   Freeze/Load/Snap/SliceView/ViewLen/ArrayLen: res, a
//   ViewSlice: res, mut, a (view), lo, hi, org
//   Index: res, a (view), b (index), org     Push: res, a (ref), b (value), org
//   Call: res, idx (function), vals, org     Arr: res, ty, vals      Fill: res, ty, a
//   Init: idx (slot), a, org      Store/Append: a (ref), b, org
//   Enter/Leave: idx (scope)      Print: parts, org
//   Br: idx (block), vals         CondBr: a, idx (true block), vals, idx2, vals2
//   Ret: vals, org                Abort: abort, org        Exit: a, org
// The low stage adds, over scalar and address values (flag on Bin/Un/Conv
// says the operation is the runtime's checked one, off says it wraps):
//   PtrOffset: res, a (address), b (i64 index), idx (element size in bytes)
//   PLoad: res, ty, a (address)             PStore: ty, a (address), b (value)
//   FrameAddr: res, idx (frame member)      LocalGet: res, idx          LocalSet: idx, a
//   StackAt: res, a (i64 base), idx (offset)  StackMark: res, a (stack)
//   StackRelease: a (stack), b (mark)       StackBump: a (stack), b (i64 bytes) or -1 and idx (bytes)
//   GlobalAddr/GlobalStack: res, idx (low global)
//   HdrBase/HdrLen: res, a (header)         HdrInit: a (header), b (base)   HdrSetLen: a, b
//   BytesCopy/BytesMove: a (dst), b (src), vals[0] (i64 byte count)
//   BytesFill: a (dst), b (src), idx (element size), vals[0] (i64 count)
//   RtCall: idx (runtime entry point), a (argument, or -1), text
//   Abort in the low stage names its operands in `vals`; its text is a user
//   abort's message.
struct GirInst {
    GirOp op = GirOp::Unit;
    int res = -1;
    GirTypeId ty = -1, ty2 = -1;
    string text;
    bool flag = false;
    CoreBinOp bin = CoreBinOp::Add;
    CoreUnOp un = CoreUnOp::Neg;
    CoreCmpOp cmp = CoreCmpOp::Eq;
    CoreConvKind conv = CoreConvKind::Widen;
    CoreMut mut = CoreMut::Mut;
    GirAbortKind abort = GirAbortKind::Assert;
    int idx = -1, idx2 = -1;
    int a = -1, b = -1;
    GirBound lo, hi;
    vector<int> vals, vals2;
    vector<GirPart> parts;
    int org = -1;
};

// Whether an instruction defines a value: a call of a function with no result
// in the low stage does not.
inline bool GirDefinesValue(const GirInst &i) {
    return GirDefines(i.op) && !(i.op == GirOp::Call && i.res < 0);
}

struct GirBlock {
    vector<pair<int, GirTypeId>> params;
    vector<GirInst> insts;
};

struct GirSlot {
    GirTypeId ty = -1;
    CoreVarKind kind = CoreVarKind::Let;
    int scope = 0;
    int var = 0;
};

// A member of a low function's frame: a scalar, a block of bytes, or the
// header of a resizable. A header's elements are on the data stack
// `stack` of the function, numbered from its hidden base argument.
struct GirMember {
    enum Kind : uint8_t { Scalar, Bytes, Header } kind = Scalar;
    GirTypeId ty = -1;     // Scalar
    int64_t size = 0;      // Bytes
    int scope = 0;         // The scope whose entry and exit bound its life.
    int stack = -1;        // Header
    string name;
};

struct GirFunc {
    string name;
    vector<GirTypeId> params, results;
    vector<GirSlot> slots;
    vector<int> scopes;   // The parent of each scope, or -1.
    vector<GirBlock> blocks;
    CoreSummary summary;
    int org = -1;         // -1 for none.
    // The low stage: the frame, and how many data stacks the function owns.
    vector<GirMember> members;
    int stacks = 0;
};

struct GirGlobal {
    string name;
    GirTypeId ty = -1;
    CoreVarKind kind = CoreVarKind::Let;
    GirFunc init;
    int org = 0;
};

// Storage of a global in the low stage.
struct GirLowGlobal {
    string name;
    GirMember::Kind kind = GirMember::Scalar;
    GirTypeId ty = -1;     // Scalar
    int64_t size = 0;      // Bytes
};

struct GirModule {
    vector<string> files;
    vector<string> diagfiles;   // As the compiler writes them in a runtime diagnostic.
    vector<CoreType> types;
    vector<GirGlobal> globals;
    vector<GirFunc> funcs;
    int entry = 0;
    vector<CoreOrigin> origins;   // File indices are those of `files`.
    // The low stage: globals' storage, the functions that initialize them in
    // order, and the data stacks the program starts with.
    bool low = false;
    vector<GirLowGlobal> lowglobals;
    vector<int> initfuncs;
    int mainstacks = 0;
    int globalstacks = 0;

    GirTypeId Intern(const CoreType &t) {
        for (size_t i = 0; i < types.size(); i++)
            if (types[i] == t) return (GirTypeId)i;
        types.push_back(t);
        return (GirTypeId)types.size() - 1;
    }
    GirTypeId IntType(CoreIntTy t) { CoreType c; c.kind = CoreType::Int; c.ity = t; return Intern(c); }
    GirTypeId BoolType() { CoreType c; c.kind = CoreType::Bool; return Intern(c); }
    GirTypeId UnitType() { CoreType c; c.kind = CoreType::Unit; return Intern(c); }
    GirTypeId RefType(CoreMut m, GirTypeId e) {
        CoreType c; c.kind = CoreType::Ref; c.mut = m; c.elem = e; return Intern(c);
    }
    GirTypeId SliceType(CoreMut m, GirTypeId e) {
        CoreType c; c.kind = CoreType::Slice; c.mut = m; c.elem = e; return Intern(c);
    }
    GirTypeId PtrType() { CoreType c; c.kind = CoreType::Ptr; return Intern(c); }
    GirTypeId ViewType(CoreMut m, GirTypeId e) {
        CoreType c; c.kind = CoreType::View; c.mut = m; c.elem = e; return Intern(c);
    }
    const CoreType &Type(GirTypeId t) const { return types[t]; }
};

inline bool GirMutAtLeast(CoreMut have, CoreMut want) {
    return have == CoreMut::Mut || want == CoreMut::Const;
}

}  // namespace goose
