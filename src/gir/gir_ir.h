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
    Snap, SliceView, ViewLen, ViewSlice, ArrayLen, Index, IndexProven, Push, Pop, Call, Arr, Fill,
    Struct, Field, Bytes, Result, DestOpen, DestChild, DestFinish, DestNamed, ResultExitDest,
    DestAbandonNamed, DestArg, DestAbandon, DestValue, DestRelocate, DestStage, DestFit,
    CallConstruct, TargetDest, Render, DestPublishRef, DestAdapt, DestAdaptFinish,
    // Instructions that define a value, low stage.
    PtrOffset, PLoad, FrameAddr, LocalGet, StackAt, StackMark, GlobalAddr, GlobalStack, HdrBase,
    HdrLen, StaticBytes, ReturnFlagGet, TargetLoad, Format, TraceId, PtrEq, SourceNew, SourceChild, SourceParam, SourceEnter, SourceCallPush, SourceCallGet, SourceGlobal, SourceTargetEnter, SourceTargetGet,
    // Instructions that define none, high stage.
    Init, Store, Append, AppendValue, PopN, Resize, Clear, Replace, DestWrite, DestAttach,
    DestBytes, DestText, DestCopy, DestRepeat, DestSnapshot, DestBind, DestPublish, DestCancel, Enter, Leave, Print,
    // Instructions that define none, low stage.
    PStore, LocalSet, StackRelease, StackBump, HdrInit, HdrSetLen, BytesCopy, BytesMove,
    BytesFill, RtCall, ReturnFlagSet, TargetStore, OutBytes, Event, SourceLeave, SourceCallPop, SourceResult, SourceCopy, SourceGlobalSet, SourceTargetLeave, SourceTargetResult,
    // Terminators.
    Br, CondBr, Invoke, Ret, Escape, Abort, Exit, Unreachable,
};

inline bool GirDefines(GirOp op) { return op <= GirOp::SourceTargetGet; }
inline bool GirIsTerminator(GirOp op) { return op >= GirOp::Br; }

// Whether an instruction belongs to the high stage only, the low stage only,
// or both (scalar arithmetic, calls and control flow).
inline bool GirHighOnly(GirOp op) {
    switch (op) {
        case GirOp::BoolCmp: case GirOp::Next: case GirOp::Slot: case GirOp::Global: case GirOp::Elem:
        case GirOp::Freeze: case GirOp::Load: case GirOp::Snap: case GirOp::SliceView:
        case GirOp::ViewLen: case GirOp::ViewSlice: case GirOp::ArrayLen: case GirOp::Index:
        case GirOp::IndexProven:
        case GirOp::Push: case GirOp::Pop: case GirOp::Arr: case GirOp::Fill: case GirOp::Struct: case GirOp::Field:
        case GirOp::DestOpen: case GirOp::DestFinish: case GirOp::DestWrite:
        case GirOp::DestBytes: case GirOp::DestPublish:
        case GirOp::Bytes: case GirOp::Result: case GirOp::DestChild: case GirOp::DestNamed:
        case GirOp::ResultExitDest: case GirOp::DestAbandonNamed: case GirOp::DestArg:
        case GirOp::DestAbandon: case GirOp::DestValue: case GirOp::DestRelocate:
        case GirOp::DestStage: case GirOp::DestFit: case GirOp::CallConstruct:
        case GirOp::TargetDest: case GirOp::Render: case GirOp::DestPublishRef: case GirOp::DestAdapt: case GirOp::DestAdaptFinish: case GirOp::AppendValue: case GirOp::DestAttach:
        case GirOp::DestText: case GirOp::DestCopy: case GirOp::DestRepeat: case GirOp::DestSnapshot: case GirOp::DestBind:
        case GirOp::DestCancel: case GirOp::Invoke: case GirOp::Escape:
        case GirOp::Unit: case GirOp::Init:
        case GirOp::Store: case GirOp::Append: case GirOp::PopN: case GirOp::Resize: case GirOp::Clear:
        case GirOp::Replace: case GirOp::Enter: case GirOp::Leave: case GirOp::Print:
            return true;
        default: return false;
    }
}
inline bool GirLowOnly(GirOp op) {
    return (op >= GirOp::PtrOffset && op <= GirOp::SourceTargetGet) ||
           (op >= GirOp::PStore && op <= GirOp::SourceTargetResult);
}

enum class GirAbortKind : uint8_t {
    DivZero, DivOverflow, IndexOob, SliceOob, Assert, UserAbort, IntOverflow, CastRange,
    PopEmpty, PopNRange, ResizeNegative, ResizeFill, Capacity,
};

// An array view is either taken directly from its owner or borrowed through a
// reference. Direct owners remain writable even when their variable binding is
// immutable; borrowed views inherit the reference's mutability.
enum class GirSnapshotMode : uint8_t { Owner, Borrowed };

enum class GirFormatKind : uint8_t { Int, Uint, Bool };
enum class GirTraceKind : uint8_t { Storage, Destination };
enum class GirEventKind : uint8_t { Begin, Write, Publish, Copy, Relocate, Stage, Abandon };
enum class GirEventReason : uint8_t { None, Storage, Repeat, HeaderRemoval, ExitValue, CapacityCheck };

inline const char *GirFormatName(GirFormatKind kind) {
    static const char *names[] = { "int", "uint", "bool" };
    return names[(int)kind];
}
inline const char *GirTraceName(GirTraceKind kind) {
    static const char *names[] = { "storage", "destination" };
    return names[(int)kind];
}
inline const char *GirEventName(GirEventKind kind) {
    static const char *names[] = { "begin", "write", "publish", "copy", "relocate", "stage", "abandon" };
    return names[(int)kind];
}
inline const char *GirEventReasonName(GirEventReason reason) {
    static const char *names[] = { "", "storage", "repeat", "header-removal", "exit-value", "capacity-check" };
    return names[(int)reason];
}

inline const char *GirAbortKindName(GirAbortKind k) {
    static const char *names[] = { "div_zero", "div_overflow", "index_oob", "slice_oob", "assert",
                                   "user_abort", "int_overflow", "cast_range", "pop_empty", "pop_n_range",
                                   "resize_negative", "resize_fill", "capacity" };
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

struct GirDestSlotReceiver {
    int slot = -1;
};

struct GirDestWholeReceiver {
    int reference = -1;
};

struct GirDestGlobalReceiver { int global = -1; };
struct GirDestPushReceiver { int reference = -1; };
struct GirDestAppendReceiver { int reference = -1; };
struct GirDestArgReceiver { int function = -1; int parameter = -1; };

using GirDestReceiver = variant<GirDestSlotReceiver, GirDestWholeReceiver, GirDestGlobalReceiver,
                                GirDestPushReceiver, GirDestAppendReceiver, GirDestArgReceiver>;

struct GirEscapeEdge {
    int target = -1;
    int block = -1;
    vector<int> forwarded;
};

struct GirResultProtocol {
    CoreRequest request = CoreRequest::Register;
    optional<int> namedSlot;
    bool operator==(const GirResultProtocol &) const = default;
};

struct GirLowChannel {
    int position = -1;
    vector<int> incoming;
    vector<int> escaped;
};

struct GirLowTarget {
    vector<int> members;
    vector<GirTypeId> cells;
    vector<GirLowChannel> channels;
};

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
    GirSnapshotMode snap = GirSnapshotMode::Borrowed;
    GirAbortKind abort = GirAbortKind::Assert;
    CoreRequest request = CoreRequest::Value;
    GirFormatKind format = GirFormatKind::Int;
    GirTraceKind trace = GirTraceKind::Storage;
    GirEventKind event = GirEventKind::Begin;
    GirEventReason reason = GirEventReason::None;
    optional<int> knownCount;
    GirDestReceiver destReceiver = GirDestSlotReceiver {};
    int idx = -1, idx2 = -1;
    int a = -1, b = -1;
    vector<uint8_t> bytes;
    GirBound lo, hi;
    vector<int> vals, vals2, forwarded;
    vector<GirEscapeEdge> escapes;
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

struct GirFact {
    enum Kind : uint8_t { Ge0, Lt, LenGe, ViewLenGe } kind = Ge0;
    // Ge0 uses `a`; the other facts use `a`, `b`.
    int a = 0, b = 0;

    bool operator==(const GirFact &other) const {
        return kind == other.kind && a == other.a && b == other.b;
    }
};

struct GirFactCertificate {
    // One asserted entry fact set per function block.
    vector<vector<GirFact>> blocks;
};

// Root annotations merged from every Core context that specializes this
// implementation. Parameter indices are positional in GIR.
struct GirRootInfo {
    vector<pair<int, vector<CoreRootRef>>> params;
    vector<pair<int, vector<CoreRootRef>>> contents;
    vector<vector<CoreRootRef>> results;
};

// A member of a low function's frame: a scalar, a block of bytes, or the
// header of a resizable. A header's elements are on the data stack
// `stack` of the function, numbered from its hidden base argument.
struct GirMember {
    enum Kind : uint8_t { Scalar, Bytes, Header, Dynamic } kind = Scalar;
    GirTypeId ty = -1;     // Scalar
    int64_t size = 0;      // Bytes
    int scope = 0;         // The scope whose entry and exit bound its life.
    int stack = -1;        // Header
    string name;
};

struct GirLowScalarResult { GirTypeId type; int output; };
struct GirLowSnapshotResult { int64_t bytes; int output; };
struct GirLowReferenceResult { int output; };
struct GirLowResizableReferenceResult { int header, stack; };
struct GirLowSliceResult { int data, count; };
struct GirLowNonfixedResult { CoreRequest request; int stack, start, count; };
using GirLowResultLayout = variant<GirLowScalarResult, GirLowSnapshotResult, GirLowReferenceResult,
    GirLowResizableReferenceResult, GirLowSliceResult, GirLowNonfixedResult>;
struct GirLowResult {
    int sourceType;
    GirLowResultLayout layout;
};

struct GirFunc {
    string name;
    vector<GirTypeId> params, results;
    vector<GirResultProtocol> resultProtocols;
    optional<vector<GirLowResult>> lowResults;
    vector<GirSlot> slots;
    GirRootInfo roots;
    vector<int> scopes;   // The parent of each scope, or -1.
    vector<GirBlock> blocks;
    optional<GirFactCertificate> certificate;
    CoreSummary summary;
    int org = -1;         // -1 for none.
    // The low stage: the frame, and how many data stacks the function owns.
    vector<GirMember> members;
    int stacks = 0;
    // What names it in emitted text: the stable key of its context and the
    // module of its declaration. Not part of the wire format.
    string key, module;
};

struct GirGlobal {
    string name;
    GirTypeId ty = -1;
    CoreVarKind kind = CoreVarKind::Let;
    GirFunc init;
    int org = 0;
    string module;
};

// Storage of a global in the low stage.
struct GirLowGlobal {
    string name;
    GirMember::Kind kind = GirMember::Scalar;
    GirTypeId ty = -1;     // Scalar
    int64_t size = 0;      // Bytes
    int stack = -1;
    string module;
};

struct GirModule {
    vector<string> files;
    vector<string> diagfiles;   // As the compiler writes them in a runtime diagnostic.
    vector<string> filemodules; // The module of each file.
    vector<CoreType> types;
    CoreProfile profile = CoreProfile::Pilot;
    vector<CoreStruct> structs;
    vector<CoreTargetSet> targets;
    vector<GirGlobal> globals;
    vector<GirFunc> funcs;
    int entry = 0;
    vector<CoreOrigin> origins;   // File indices are those of `files`.
    // The low stage: globals' storage, the functions that initialize them in
    // order, and the data stacks the program starts with.
    bool low = false;
    vector<GirLowGlobal> lowglobals;
    vector<GirLowTarget> lowtargets;
    vector<int> initfuncs;
    int mainstacks = 0;
    int globalstacks = 0;
    int pointerBytes = sizeof(void *);

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
    GirTypeId CarrierType(CoreType::Kind kind, GirTypeId type, CoreRequest request) {
        CoreType carrier;
        carrier.kind = kind;
        carrier.elem = type;
        carrier.request = request;
        return Intern(carrier);
    }
    GirTypeId TupleType(vector<GirTypeId> parts) {
        CoreType tuple;
        tuple.kind = CoreType::Tuple;
        tuple.parts = std::move(parts);
        return Intern(tuple);
    }
    const CoreType &Type(GirTypeId t) const { return types[t]; }
};

enum class GirSourceKind : int { Unknown = -1, Ordinary, Descriptor, Scope, Call, Target, Mixed };

struct GirSourceClassification {
    vector<GirSourceKind> values, members;
};

inline GirSourceClassification GirSourceKinds(const GirFunc &function) {
    int count = 0;
    for (auto &block : function.blocks) {
        count += (int)block.params.size();
        for (auto &instruction : block.insts) count += GirDefinesValue(instruction);
    }
    GirSourceClassification kinds { vector<GirSourceKind>(count, GirSourceKind::Ordinary), vector<GirSourceKind>(function.members.size(), GirSourceKind::Unknown) };
    for (size_t block = 1; block < function.blocks.size(); block++)
        for (auto &parameter : function.blocks[block].params) kinds.values[parameter.first] = GirSourceKind::Unknown;
    for (auto &block : function.blocks) for (auto &instruction : block.insts) {
        switch (instruction.op) {
            case GirOp::SourceNew: case GirOp::SourceChild: case GirOp::SourceParam: case GirOp::SourceCallGet: case GirOp::SourceGlobal: case GirOp::SourceTargetGet:
                kinds.values[instruction.res] = GirSourceKind::Descriptor; break;
            case GirOp::SourceTargetEnter: kinds.values[instruction.res] = GirSourceKind::Target; break;
            case GirOp::SourceEnter: kinds.values[instruction.res] = GirSourceKind::Scope; break;
            case GirOp::SourceCallPush: kinds.values[instruction.res] = GirSourceKind::Call; break;
            case GirOp::LocalGet: kinds.values[instruction.res] = GirSourceKind::Unknown; break;
            default: break;
        }
    }
    auto merge = [](GirSourceKind current, GirSourceKind value) {
        if (value == GirSourceKind::Unknown) return current;
        if (current == GirSourceKind::Unknown) return value;
        return current == value ? current : GirSourceKind::Mixed;
    };
    for (int round = 0; round < count * 4 + 8; round++) {
        auto previous = kinds;
        fill(kinds.members.begin(), kinds.members.end(), GirSourceKind::Unknown);
        for (auto &block : function.blocks) for (auto &instruction : block.insts)
            if (instruction.op == GirOp::LocalSet)
                kinds.members[instruction.idx] = merge(kinds.members[instruction.idx], kinds.values[instruction.a]);
        for (auto &block : function.blocks) for (auto &instruction : block.insts) {
            if (instruction.op == GirOp::LocalGet) kinds.values[instruction.res] = kinds.members[instruction.idx];
            auto edge = [&](int target, const vector<int> &values) {
                for (size_t position = 0; position < values.size(); position++) {
                    auto parameter = function.blocks[target].params[position].first;
                    kinds.values[parameter] = merge(kinds.values[parameter], kinds.values[values[position]]);
                }
            };
            if (instruction.op == GirOp::Br || instruction.op == GirOp::CondBr) edge(instruction.idx, instruction.vals);
            if (instruction.op == GirOp::CondBr) edge(instruction.idx2, instruction.vals2);
        }
        if (previous.values == kinds.values && previous.members == kinds.members) break;
    }
    return kinds;
}

inline bool GirMutAtLeast(CoreMut have, CoreMut want) {
    return have == CoreMut::Mut || want == CoreMut::Const;
}

}  // namespace goose
