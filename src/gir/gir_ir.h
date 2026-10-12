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
    // Instructions that define a value.
    Int, Bool, Unit, Bin, Un, Cmp, BoolCmp, Not, Conv, Next, Slot, Global, Elem, Freeze, Load,
    Snap, SliceView, ViewLen, ViewSlice, ArrayLen, Index, Push, Call, Arr, Fill,
    // Instructions that define none.
    Init, Store, Append, Enter, Leave, Print,
    // Terminators.
    Br, CondBr, Ret, Abort, Exit,
};

inline bool GirDefines(GirOp op) { return op <= GirOp::Fill; }
inline bool GirIsTerminator(GirOp op) { return op >= GirOp::Br; }

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

struct GirFunc {
    string name;
    vector<GirTypeId> params, results;
    vector<GirSlot> slots;
    vector<int> scopes;   // The parent of each scope, or -1.
    vector<GirBlock> blocks;
    CoreSummary summary;
    int org = -1;         // -1 for none.
};

struct GirGlobal {
    string name;
    GirTypeId ty = -1;
    CoreVarKind kind = CoreVarKind::Let;
    GirFunc init;
    int org = 0;
};

struct GirModule {
    vector<string> files;
    vector<CoreType> types;
    vector<GirGlobal> globals;
    vector<GirFunc> funcs;
    int entry = 0;
    vector<CoreOrigin> origins;   // File indices are those of `files`.

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
    GirTypeId ViewType(CoreMut m, GirTypeId e) {
        CoreType c; c.kind = CoreType::View; c.mut = m; c.elem = e; return Intern(c);
    }
    const CoreType &Type(GirTypeId t) const { return types[t]; }
};

inline bool GirMutAtLeast(CoreMut have, CoreMut want) {
    return have == CoreMut::Mut || want == CoreMut::Const;
}

}  // namespace goose
