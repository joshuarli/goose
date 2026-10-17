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
    Int, Bool, Unit, Bin, Un, Cmp, BoolCmp, Not, Conv, Next, Slot, Global, Elem, Freeze, OwnerBorrow, Load,
    Snap, SliceView, ViewLen, ViewSlice, ArrayLen, Index, IndexProven, Push, Pop, Call, Arr, Fill,
    Struct, Field, Bytes, Result, DestOpen, DestChild, DestFinish,
    DestArg, DestAbandon, DestValue, DestRelocate, DestStage, DestFit,
    CallConstruct, Render, DestPublishRef, DestPrepareNamed, DestAdapt, DestAdaptFinish,
    ReceivingOpen, TargetReceiving, DestRenew, DestRefresh, ExitWait, ExitReserve, ExitIsNamed, ReservedDest, ReservedNamed,
    ExitLand, ExitAdopt, ReceivingCancel,
    // Instructions that define a value, low stage.
    PtrOffset, PLoad, FrameAddr, LocalGet, StackAt, StackMark, GlobalAddr, GlobalStack, HdrBase,
    HdrLen, StaticBytes, ReturnFlagGet, TargetLoad, Format, TraceId, PtrEq, SourceNew, SourceChild, SourceParam, SourceEnter, SourceCallPush, SourceCallGet, SourceGlobal, SourceTargetEnter, SourceTargetGet,
    ControlEnter, ControlCallPush, ControlCallParam, ControlCallGet, ControlOwnerNone, ControlOwnerIsNamed, ControlNamedBase, ControlNamedCount, ControlNamedBind, ControlOwnerBind, ControlOwnerParam, ControlOwnerGet, ControlOwnerTargetEnter, ControlOwnerTargetGet, ControlReceivingNew, ControlReceivingOpen, ControlReceivingCurrent,
    ControlReceivingRenew, ControlReceivingRefresh, ControlAttemptStack, ControlAttemptStart,
    ControlAttemptProgress, ControlAttemptPrefix, ControlAttemptMode, ControlAttemptReceiving,
    ControlExitWait, ControlExitReserve, ControlExitIsNamed, ControlExitAdopt, ControlExitSelected, ControlExitPrepare, ControlExitCommit,
    ControlReceivingCancel, ControlAttemptAbandon,
    // Instructions that define none, high stage.
    Init, Store, Append, AppendValue, PopN, Resize, Clear, Replace, DestWrite, DestAttach,
    DestBytes, DestText, DestCopy, DestRepeat, DestSnapshot, DestBind, DestPublish, DestCancel, Enter, Leave, Print,
    ExitSelect, ExitRearm, ExitRelease, ExitDiscard, ExitMarkNamed, ReceivingDrop,
    // Instructions that define none, low stage.
    PStore, LocalSet, StackRelease, StackBump, HdrInit, HdrSetLen, BytesCopy, BytesMove,
    BytesFill, RtCall, ReturnFlagSet, TargetStore, OutBytes, Event, SourceLeave, SourceCallPop, SourceResult, SourceCopy, SourceGlobalSet, SourceTargetLeave, SourceTargetResult,
    ControlLeave, ControlCallPop, ControlOwnerCheck, ControlOwnerExtend, ControlOwnerUpdate, ControlOwnerResult, ControlOwnerTargetResult, ControlOwnerTargetLeave, ControlReceivingDrop, ControlReceivingTransfer, ControlExitSelect, ControlExitRearm, ControlExitMarkNamed, ControlExitRelease, ControlExitDiscard, ControlAttemptCancel,
    ControlAttemptPrepareNamed, ControlAttemptNormalize, ControlAttemptPack, ControlAttemptRemoveHeader, ControlAttemptChild, ControlAttemptFinish, ControlAttemptAttach, ControlAttemptPublish, ControlAttemptReturn,
    // Terminators.
    Br, CondBr, Invoke, Ret, Escape, Abort, Exit, Unreachable,
};

inline bool GirDefines(GirOp op) { return op <= GirOp::ControlAttemptAbandon; }
inline bool GirIsTerminator(GirOp op) { return op >= GirOp::Br; }

// Whether an instruction belongs to the high stage only, the low stage only,
// or both (scalar arithmetic, calls and control flow).
inline bool GirHighOnly(GirOp op) {
    switch (op) {
        case GirOp::BoolCmp: case GirOp::Next: case GirOp::Slot: case GirOp::Global: case GirOp::Elem:
        case GirOp::Freeze: case GirOp::OwnerBorrow: case GirOp::Load: case GirOp::Snap: case GirOp::SliceView:
        case GirOp::ViewLen: case GirOp::ViewSlice: case GirOp::ArrayLen: case GirOp::Index:
        case GirOp::IndexProven:
        case GirOp::Push: case GirOp::Pop: case GirOp::Arr: case GirOp::Fill: case GirOp::Struct: case GirOp::Field:
        case GirOp::DestOpen: case GirOp::DestFinish: case GirOp::DestWrite:
        case GirOp::DestBytes: case GirOp::DestPublish:
        case GirOp::Bytes: case GirOp::Result: case GirOp::DestChild:
        case GirOp::DestArg:
        case GirOp::DestAbandon: case GirOp::DestValue: case GirOp::DestRelocate:
        case GirOp::DestStage: case GirOp::DestFit: case GirOp::CallConstruct:
        case GirOp::Render: case GirOp::DestPublishRef: case GirOp::DestPrepareNamed: case GirOp::DestAdapt: case GirOp::DestAdaptFinish: case GirOp::AppendValue: case GirOp::DestAttach:
        case GirOp::DestText: case GirOp::DestCopy: case GirOp::DestRepeat: case GirOp::DestSnapshot: case GirOp::DestBind:
        case GirOp::ReceivingOpen: case GirOp::TargetReceiving: case GirOp::DestRenew: case GirOp::DestRefresh:
        case GirOp::ExitWait: case GirOp::ExitReserve: case GirOp::ExitSelect: case GirOp::ExitIsNamed: case GirOp::ReservedDest: case GirOp::ReservedNamed:
        case GirOp::ExitLand: case GirOp::ExitAdopt: case GirOp::ReceivingCancel:
        case GirOp::ExitRearm: case GirOp::ExitRelease: case GirOp::ExitDiscard: case GirOp::ExitMarkNamed: case GirOp::ReceivingDrop:
        case GirOp::DestCancel: case GirOp::Invoke: case GirOp::Escape:
        case GirOp::Unit: case GirOp::Init:
        case GirOp::Store: case GirOp::Append: case GirOp::PopN: case GirOp::Resize: case GirOp::Clear:
        case GirOp::Replace: case GirOp::Enter: case GirOp::Leave: case GirOp::Print:
            return true;
        default: return false;
    }
}
inline bool GirLowOnly(GirOp op) {
    return (op >= GirOp::PtrOffset && op <= GirOp::ControlAttemptAbandon) ||
           (op >= GirOp::PStore && op <= GirOp::ControlAttemptReturn);
}

enum class GirAbortKind : uint8_t {
    DivZero, DivOverflow, IndexOob, SliceOob, Assert, UserAbort, IntOverflow, CastRange,
    PopEmpty, PopNRange, ResizeNegative, ResizeFill, Capacity,
};

// An array view is either taken directly from its owner or borrowed through a
// reference. Direct owners remain writable even when their variable binding is
// immutable; borrowed views inherit the reference's mutability.
enum class GirSnapshotMode : uint8_t { Owner, Borrowed };
struct GirExitNewValue { bool operator==(const GirExitNewValue &) const = default; };
struct GirExitNamedAlias { int binding; bool operator==(const GirExitNamedAlias &) const = default; };
using GirExitSource = variant<GirExitNewValue, GirExitNamedAlias>;

inline optional<int> GirNamedExitBinding(const GirExitSource &source) {
    if (auto alias = get_if<GirExitNamedAlias>(&source)) return alias->binding;
    return nullopt;
}

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

enum class GirConstructionIncomingWord : size_t { Stack, Start, Metadata, Progress, Receiving, Count };
enum class GirConstructionEscapedWord : size_t { Start, End, Count, Identity, Replacement, WordCount };
inline constexpr size_t GirConstructionOutputWords = 4;
inline constexpr size_t GirConstructionTargetIncomingWords = (size_t)GirConstructionIncomingWord::Count;
inline constexpr size_t GirConstructionEscapedWords = (size_t)GirConstructionEscapedWord::WordCount;

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
    GirExitSource exitSource = GirExitNewValue {};
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
    vector<optional<int>> ownerBindings, ownerPositions;
    vector<GirEscapeEdge> escapes;
    vector<GirPart> parts;
    int org = -1;
};

enum class GirControlForm : uint8_t { None, Parameter, Call, Operand, OperandParameter, Pair, Values, OperandValues, PairValues, Source, TargetPositions, TargetResult };

struct GirControlContract {
    const char *wire;
    GirControlForm form;
    optional<CoreType::Kind> result;
    vector<CoreType::Kind> inputs;
    optional<CoreType::Kind> repeatedInput;
};

inline optional<GirControlContract> GirControlOf(GirOp op) {
    using Form = GirControlForm;
    using Kind = CoreType;
    switch (op) {
        case GirOp::ControlEnter: return GirControlContract { "l_control_enter", Form::None, Kind::Ptr, {}, nullopt };
        case GirOp::ControlCallPush: return GirControlContract { "l_control_call_push", Form::Call, Kind::Ptr, {}, Kind::Ptr };
        case GirOp::ControlCallParam: return GirControlContract { "l_control_call_param", Form::Parameter, Kind::Ptr, {}, nullopt };
        case GirOp::ControlCallGet: return GirControlContract { "l_control_call_get", Form::OperandParameter, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlOwnerIsNamed: return GirControlContract { "l_control_owner_is_named", Form::Operand, Kind::Bool, { Kind::Ptr }, nullopt };
        case GirOp::ControlNamedBase: return GirControlContract { "l_control_named_base", Form::Pair, Kind::Ptr, { Kind::Ptr, Kind::Ptr }, nullopt };
        case GirOp::ControlNamedCount: return GirControlContract { "l_control_named_count", Form::Pair, Kind::Int, { Kind::Ptr, Kind::Ptr }, nullopt };
        case GirOp::ControlNamedBind: return GirControlContract { "l_control_named_bind", Form::Operand, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlOwnerNone: return GirControlContract { "l_control_owner_none", Form::None, Kind::Ptr, {}, nullopt };
        case GirOp::ControlOwnerTargetEnter: return GirControlContract { "l_control_owner_target_enter", Form::TargetPositions, Kind::Ptr, {}, nullopt };
        case GirOp::ControlOwnerTargetGet: return GirControlContract { "l_control_owner_target_get", Form::OperandParameter, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlOwnerTargetResult: return GirControlContract { "l_control_owner_target_result", Form::TargetResult, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlOwnerTargetLeave: return GirControlContract { "l_control_owner_target_leave", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlExitMarkNamed: return GirControlContract { "l_control_exit_mark_named", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlOwnerBind: return GirControlContract { "l_control_owner_bind", Form::PairValues, Kind::Ptr, { Kind::Ptr, Kind::Ptr, Kind::Ptr }, nullopt };
        case GirOp::ControlOwnerParam: return GirControlContract { "l_control_owner_param", Form::Parameter, Kind::Ptr, {}, nullopt };
        case GirOp::ControlOwnerGet: return GirControlContract { "l_control_owner_get", Form::OperandParameter, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlOwnerExtend: return GirControlContract { "l_control_owner_extend", Form::Pair, nullopt, { Kind::Ptr, Kind::Ptr }, nullopt };
        case GirOp::ControlOwnerCheck: return GirControlContract { "l_control_owner_check", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlOwnerUpdate: return GirControlContract { "l_control_owner_update", Form::PairValues, nullopt, { Kind::Ptr, Kind::Int, Kind::Ptr }, nullopt };
        case GirOp::ControlOwnerResult: return GirControlContract { "l_control_owner_result", Form::OperandParameter, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlReceivingNew: return GirControlContract { "l_control_receiving_new", Form::PairValues, Kind::Ptr, { Kind::Ptr, Kind::Ptr, Kind::Int, Kind::Int }, nullopt };
        case GirOp::ControlReceivingOpen: return GirControlContract { "l_control_receiving_open", Form::Operand, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlReceivingCurrent: return GirControlContract { "l_control_receiving_current", Form::Operand, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlReceivingRenew: return GirControlContract { "l_control_receiving_renew", Form::Operand, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlReceivingRefresh: return GirControlContract { "l_control_receiving_refresh", Form::PairValues, Kind::Ptr, { Kind::Ptr, Kind::Ptr, Kind::Ptr, Kind::Int }, nullopt };
        case GirOp::ControlAttemptStack: return GirControlContract { "l_control_attempt_stack", Form::Operand, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptStart: return GirControlContract { "l_control_attempt_start", Form::Operand, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptProgress: return GirControlContract { "l_control_attempt_progress", Form::Operand, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptPrefix: return GirControlContract { "l_control_attempt_prefix", Form::Operand, Kind::Int, { Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptPrepareNamed: return GirControlContract { "l_control_attempt_prepare_named", Form::Pair, nullopt, { Kind::Ptr, Kind::Int }, nullopt };
        case GirOp::ControlAttemptPack: return GirControlContract { "l_control_attempt_pack", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptRemoveHeader: return GirControlContract { "l_control_attempt_remove_header", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptNormalize: return GirControlContract { "l_control_attempt_normalize", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptMode: return GirControlContract { "l_control_attempt_mode", Form::Operand, Kind::Bool, { Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptReceiving: return GirControlContract { "l_control_attempt_receiving", Form::Operand, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlExitIsNamed: return GirControlContract { "l_control_exit_is_named", Form::Operand, Kind::Bool, { Kind::Ptr }, nullopt };
        case GirOp::ControlExitWait: return GirControlContract { "l_control_exit_wait", Form::Operand, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlExitSelect: return GirControlContract { "l_control_exit_select", Form::Source, nullopt, { Kind::Ptr }, Kind::Ptr };
        case GirOp::ControlExitReserve: return GirControlContract { "l_control_exit_reserve", Form::Source, Kind::Ptr, { Kind::Ptr }, Kind::Ptr };
        case GirOp::ControlExitAdopt: return GirControlContract { "l_control_exit_adopt", Form::Pair, Kind::Ptr, { Kind::Ptr, Kind::Ptr }, nullopt };
        case GirOp::ControlExitSelected: return GirControlContract { "l_control_exit_selected", Form::Operand, Kind::Ptr, { Kind::Ptr }, nullopt };
        case GirOp::ControlExitPrepare: return GirControlContract { "l_control_exit_prepare", Form::Pair, Kind::Ptr, { Kind::Ptr, Kind::Ptr }, nullopt };
        case GirOp::ControlExitCommit: return GirControlContract { "l_control_exit_commit", Form::PairValues, Kind::Ptr, { Kind::Ptr, Kind::Ptr, Kind::Ptr }, nullopt };
        case GirOp::ControlReceivingCancel: return GirControlContract { "l_control_receiving_cancel", Form::OperandValues, Kind::Ptr, { Kind::Ptr }, Kind::Ptr };
        case GirOp::ControlAttemptAbandon: return GirControlContract { "l_control_attempt_abandon", Form::OperandValues, Kind::Ptr, { Kind::Ptr }, Kind::Ptr };
        case GirOp::ControlLeave: return GirControlContract { "l_control_leave", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlCallPop: return GirControlContract { "l_control_call_pop", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlReceivingDrop: return GirControlContract { "l_control_receiving_drop", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlReceivingTransfer: return GirControlContract { "l_control_receiving_transfer", Form::PairValues, nullopt, { Kind::Ptr, Kind::Ptr, Kind::Bool }, nullopt };
        case GirOp::ControlExitRearm: return GirControlContract { "l_control_exit_rearm", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlExitRelease: return GirControlContract { "l_control_exit_release", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlExitDiscard: return GirControlContract { "l_control_exit_discard", Form::OperandValues, nullopt, { Kind::Ptr }, Kind::Ptr };
        case GirOp::ControlAttemptCancel: return GirControlContract { "l_control_attempt_cancel", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptChild: return GirControlContract { "l_control_attempt_child", Form::Pair, nullopt, { Kind::Ptr, Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptFinish: return GirControlContract { "l_control_attempt_finish", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptAttach: return GirControlContract { "l_control_attempt_attach", Form::Pair, nullopt, { Kind::Ptr, Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptPublish: return GirControlContract { "l_control_attempt_publish", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        case GirOp::ControlAttemptReturn: return GirControlContract { "l_control_attempt_return", Form::Operand, nullopt, { Kind::Ptr }, nullopt };
        default: return nullopt;
    }
}

inline vector<int> GirControlOperands(const GirInst &inst, GirControlForm form) {
    vector<int> operands;
    switch (form) {
        case GirControlForm::None: case GirControlForm::Parameter: case GirControlForm::TargetPositions: break;
        case GirControlForm::Operand: case GirControlForm::OperandParameter: case GirControlForm::TargetResult: operands = { inst.a }; break;
        case GirControlForm::Source:
            operands = { inst.a };
            if (auto binding = GirNamedExitBinding(inst.exitSource)) operands.push_back(*binding);
            break;
        case GirControlForm::Pair: operands = { inst.a, inst.b }; break;
        case GirControlForm::Call:
            operands = inst.vals;
            for (auto binding : inst.ownerBindings) if (binding) operands.push_back(*binding);
            break;
        case GirControlForm::Values: operands = inst.vals; break;
        case GirControlForm::OperandValues:
            operands = { inst.a };
            operands.insert(operands.end(), inst.vals.begin(), inst.vals.end());
            break;
        case GirControlForm::PairValues:
            operands = { inst.a, inst.b };
            operands.insert(operands.end(), inst.vals.begin(), inst.vals.end());
            break;
    }
    return operands;
}

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
    optional<vector<pair<int, vector<CoreRootRef>>>> slots;
    optional<vector<pair<int, vector<CoreRootRef>>>> values;
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
enum class GirConstructionProgress : int64_t {
    Open = 0, Suspended = 1, Built = 2, Published = 3, Exiting = 4,
    Abandoned = 5, Cancelled = 6, Attached = 7, Retired = 8
};

inline constexpr int64_t GirConstructionIdentityOffset = 8;
inline constexpr int64_t GirConstructionMetadataBytes = 16;
inline constexpr int64_t GirConstructionProgressBytes = 8;

struct GirLowNonfixedResult { CoreRequest request; int stack, start, count, progress; };
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
