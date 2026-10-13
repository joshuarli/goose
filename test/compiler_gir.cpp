// The GIR-H and GIR-L verifier on small modules built in memory: a module the lowering
// could produce is accepted, and each way of breaking it is rejected under the
// code that names the broken property. Keep assertions active even in an
// optimized test build.
#ifdef NDEBUG
#undef NDEBUG
#endif
#include "../src/includes.h"
#include "../src/utils.h"
#include "../src/small_vector.h"
#include "../src/lexer.h"
#include "../src/ast.h"
#include "../src/ident/sha256.h"
#include "../src/core/core_ir.h"
#include "../src/core/core_json.h"
#include "../src/gir/gir_ir.h"
#include "../src/gir/gir_types.h"
#include "../src/gir/gir_lower.h"
#include "../src/gir/gir_low.h"
#include "../src/gir/gir_json.h"
#include "../src/gir/gir_verify.h"

using namespace goose;

namespace {

GirInst Def(GirOp op, int res) {
    GirInst i;
    i.op = op;
    i.res = res;
    return i;
}

GirInst Int(GirModule &m, int res, const char *text) {
    auto i = Def(GirOp::Int, res);
    i.ty = m.IntType(CoreIntTy::I64);
    i.text = text;
    return i;
}

GirInst Enter(int scope) { GirInst i; i.op = GirOp::Enter; i.idx = scope; return i; }
GirInst Leave(int scope) { GirInst i; i.op = GirOp::Leave; i.idx = scope; return i; }
GirInst Ret(vector<int> vals = {}) { GirInst i; i.op = GirOp::Ret; i.vals = std::move(vals); return i; }
GirInst Br(int block, vector<int> args = {}) { GirInst i; i.op = GirOp::Br; i.idx = block; i.vals = std::move(args); return i; }

GirInst CondBr(int c, int t, int e) {
    GirInst i;
    i.op = GirOp::CondBr;
    i.a = c;
    i.idx = t;
    i.idx2 = e;
    return i;
}

GirInst Init(int slot, int val) {
    GirInst i;
    i.op = GirOp::Init;
    i.idx = slot;
    i.a = val;
    i.org = 0;
    return i;
}

// A module of one function, the entry, whose one block ends in `ret`.
GirModule Base() {
    GirModule m;
    m.files = { "t.goose" };
    m.origins = { CoreOrigin { 0, 1, CoreOriginKind::Let } };
    GirFunc f;
    f.name = "main";
    f.scopes = { -1 };
    GirBlock b;
    b.insts = { Enter(0), Leave(0), Ret() };
    f.blocks = { b };
    m.funcs = { f };
    return m;
}

GirFunc &Main(GirModule &m) { return m.funcs[0]; }

string Code(GirModule m) {
    auto v = GirVerifier(m).Verify();
    return v ? v->code : "";
}

// The module with one more slot, `let` or `var`, in scope 0.
void AddSlot(GirModule &m, CoreVarKind kind) {
    Main(m).slots.push_back({ m.IntType(CoreIntTy::I64), kind, 0, 0 });
}

void Accepts() {
    auto m = Base();
    assert(Code(m) == "");
    // A slot initialized and stored through, with a branch and a join.
    AddSlot(m, CoreVarKind::Var);
    auto &b = Main(m).blocks;
    GirBlock b0, b1;
    GirInst boolean = Def(GirOp::Bool, 1);
    boolean.flag = true;
    GirInst slot = Def(GirOp::Slot, 2);
    slot.idx = 0;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 2;
    store.b = 0;
    store.org = 0;
    b0.insts = { Enter(0), Int(m, 0, "1"), Init(0, 0), boolean, slot, store, Leave(0), Ret() };
    b = { b0 };
    (void)b1;
    assert(Code(m) == "");
}

void RejectsUseNotDominatedByDefinition() {
    auto m = Base();
    auto &f = Main(m);
    GirInst cond = Def(GirOp::Bool, 0);
    GirInst print;
    print.op = GirOp::Print;
    print.org = 0;
    print.parts = { { false, "", 1 } };
    GirBlock b0, b1, b2, b3;
    b0.insts = { cond, CondBr(0, 1, 2) };
    b1.insts = { Int(m, 1, "1"), Br(3) };
    b2.insts = { Br(3) };
    b3.insts = { print, Ret() };
    f.blocks = { b0, b1, b2, b3 };
    f.summary.outputs = true;
    assert(Code(m) == "GIR-V020");
}

void RejectsWrongEdgeArgumentType() {
    auto m = Base();
    auto &f = Main(m);
    GirBlock b0, b1;
    b0.insts = { Int(m, 0, "1"), Br(1, { 0 }) };
    b1.params = { { 1, m.BoolType() } };
    b1.insts = { Ret() };
    f.blocks = { b0, b1 };
    assert(Code(m) == "GIR-V020");
}

void RejectsBlockWithTwoTerminatorsOrNone() {
    auto m = Base();
    Main(m).blocks[0].insts = { Ret(), Ret() };
    assert(Code(m) == "GIR-V020");
    auto n = Base();
    Main(n).blocks[0].insts = { Enter(0), Leave(0) };
    assert(Code(n) == "GIR-V020");
}

void RejectsStoreThroughConst() {
    auto m = Base();
    AddSlot(m, CoreVarKind::Let);
    GirInst slot = Def(GirOp::Slot, 1);
    slot.idx = 0;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 1;
    store.b = 0;
    store.org = 0;
    Main(m).blocks[0].insts = { Enter(0), Int(m, 0, "1"), Init(0, 0), slot, store, Leave(0), Ret() };
    assert(Code(m) == "GIR-V030");
}

void RejectsSlotAddressOutsideItsScope() {
    auto m = Base();
    AddSlot(m, CoreVarKind::Var);
    GirInst slot = Def(GirOp::Slot, 0);
    slot.idx = 0;
    Main(m).blocks[0].insts = { slot, Enter(0), Leave(0), Ret() };
    assert(Code(m) == "GIR-V030");
}

void RejectsLoadOfResizable() {
    auto m = Base();
    CoreType grow;
    grow.kind = CoreType::Grow;
    grow.elem = m.IntType(CoreIntTy::I64);
    auto slotType = m.Intern(grow);
    Main(m).slots.push_back({ slotType, CoreVarKind::Let, 0, 0 });
    GirInst slot = Def(GirOp::Slot, 0);
    slot.idx = 0;
    GirInst load = Def(GirOp::Load, 1);
    load.a = 0;
    Main(m).blocks[0].insts = { Enter(0), slot, load, Leave(0), Ret() };
    assert(Code(m) == "GIR-V030");
}

void RejectsUnbalancedScopesOnOnePath() {
    auto m = Base();
    auto &f = Main(m);
    f.scopes = { -1, 0 };
    GirInst cond = Def(GirOp::Bool, 0);
    GirBlock b0, b1, b2, b3;
    b0.insts = { Enter(0), cond, CondBr(0, 1, 2) };
    b1.insts = { Enter(1), Br(3) };
    b2.insts = { Br(3) };
    b3.insts = { Leave(0), Ret() };
    f.blocks = { b0, b1, b2, b3 };
    assert(Code(m) == "GIR-V040");
}

void RejectsReturnInsideAnEnteredScope() {
    auto m = Base();
    Main(m).blocks[0].insts = { Enter(0), Ret() };
    assert(Code(m) == "GIR-V040");
}

void RejectsSummaryThatOmitsAWrite() {
    auto m = Base();
    GirFunc f;
    f.name = "poke";
    f.scopes = { -1 };
    auto i64 = m.IntType(CoreIntTy::I64);
    f.params = { m.RefType(CoreMut::Mut, i64) };
    GirBlock b;
    b.params = { { 0, f.params[0] } };
    GirInst store;
    store.op = GirOp::Store;
    store.a = 0;
    store.b = 1;
    store.org = 0;
    b.insts = { Enter(0), Int(m, 1, "1"), store, Leave(0), Ret() };
    f.blocks = { b };
    m.funcs.push_back(f);
    assert(Code(m) == "GIR-V050");
    // Declared, it is accepted.
    m.funcs[1].summary.writes = { CoreTarget { false, 0 } };
    assert(Code(m) == "");
}

void RejectsCallThatPropagatesATarget() {
    auto m = Base();
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ref = m.RefType(CoreMut::Mut, i64);
    GirFunc poke;
    poke.name = "poke";
    poke.params = { ref };
    poke.scopes = { -1 };
    poke.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    poke.summary.writes = { CoreTarget { false, 0 } };
    GirBlock pokeBlock;
    pokeBlock.params = { { 0, ref } };
    GirInst store;
    store.op = GirOp::Store;
    store.a = 0;
    store.b = 1;
    store.org = 0;
    pokeBlock.insts = { Enter(0), Int(m, 1, "1"), store, Leave(0), Ret() };
    poke.blocks = { pokeBlock };
    m.funcs.push_back(poke);

    GirFunc wrapper;
    wrapper.name = "wrapper";
    wrapper.params = { ref };
    wrapper.scopes = { -1 };
    wrapper.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    GirBlock wrapperBlock;
    wrapperBlock.params = { { 0, ref } };
    GirInst call;
    call.op = GirOp::Call;
    call.idx = 1;
    call.vals = { 0 };
    call.org = 0;
    wrapperBlock.insts = { Enter(0), call, Leave(0), Ret() };
    wrapper.blocks = { wrapperBlock };
    m.funcs.push_back(wrapper);

    assert(Code(m) == "GIR-V050");
    m.funcs[2].summary.writes = { CoreTarget { false, 0 } };
    assert(Code(m) == "");
}

void RejectsSummaryThatOmitsSliceParameterRebind() {
    auto m = Base();
    auto i64 = m.IntType(CoreIntTy::I64);
    auto slice = m.SliceType(CoreMut::Mut, i64);
    auto refSlice = m.RefType(CoreMut::Mut, slice);
    GirFunc f;
    f.name = "set_slice";
    f.params = { refSlice, slice };
    f.slots = { { refSlice, CoreVarKind::Let, 0, 0 }, { slice, CoreVarKind::Let, 0, 1 } };
    f.scopes = { -1 };
    GirBlock b;
    b.params = { { 0, refSlice }, { 1, slice } };
    GirInst store;
    store.op = GirOp::Store;
    store.a = 0;
    store.b = 1;
    store.org = 0;
    b.insts = { store, Ret() };
    f.blocks = { b };
    f.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    f.roots.contents = { { 0, {} } };
    f.summary.writes = { CoreTarget { false, 0 } };
    m.funcs.push_back(f);
    assert(Code(m) == "GIR-V050");
    m.funcs[1].slots.push_back({ refSlice, CoreVarKind::Let, 0, 2 });
    assert(Code(m) == "GIR-V010");
    m.funcs[1].slots.pop_back();
    m.funcs[1].summary.rebinds = { CoreTarget { false, 0 } };
    assert(Code(m) == "");
}

void RejectsReferenceToSliceResult() {
    auto m = Base();
    auto slice = m.SliceType(CoreMut::Mut, m.IntType(CoreIntTy::I64));
    auto refSlice = m.RefType(CoreMut::Mut, slice);
    GirFunc f;
    f.name = "return_slice_reference";
    f.params = { refSlice };
    f.results = { refSlice };
    GirBlock b;
    b.params = { { 0, refSlice } };
    b.insts = { Ret({ 0 }) };
    f.blocks = { b };
    m.funcs.push_back(f);
    assert(Code(m) == "GIR-V010");
}

void RejectsReferenceToSliceGlobal() {
    auto m = Base();
    auto slice = m.SliceType(CoreMut::Mut, m.IntType(CoreIntTy::I64));
    auto refSlice = m.RefType(CoreMut::Mut, slice);
    GirGlobal g;
    g.name = "slice_reference";
    g.ty = refSlice;
    g.init.name = "slice_reference_init";
    g.init.results = { refSlice };
    GirBlock b;
    b.insts = { Ret() };
    g.init.blocks = { b };
    m.globals.push_back(g);
    assert(Code(m) == "GIR-V010");
}

void RejectsSummaryThatOmitsAGlobalReachedThroughACalleeParameter() {
    auto m = Base();
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ref = m.RefType(CoreMut::Mut, i64);
    GirGlobal g;
    g.name = "counter";
    g.ty = i64;
    g.kind = CoreVarKind::Var;
    g.org = 0;
    g.init.name = "counter";
    g.init.results = { i64 };
    g.init.roots.results = { {} };
    g.init.summary.unknown = true;
    GirBlock init;
    init.insts = { Int(m, 0, "0"), Ret({ 0 }) };
    g.init.blocks = { init };
    m.globals.push_back(g);

    GirFunc wrap;
    wrap.name = "wrap";
    wrap.params = { ref };
    wrap.scopes = { -1 };
    GirBlock wb;
    wb.params = { { 0, ref } };
    auto call = Def(GirOp::Call, 1);
    call.idx = 2;
    call.vals = { 0 };
    call.org = 0;
    wb.insts = { call, Ret() };
    wrap.blocks = { wb };
    wrap.roots.params = { { 0, { CoreRootRef { CoreRootRef::Global, 0 } } } };
    wrap.summary.reads = { CoreTarget { false, 0 } };

    GirFunc touch;
    touch.name = "touch";
    touch.params = { ref };
    touch.scopes = { -1 };
    GirBlock tb;
    tb.params = { { 0, ref } };
    auto load = Def(GirOp::Load, 1);
    load.a = 0;
    tb.insts = { load, Ret() };
    touch.blocks = { tb };
    touch.roots.params = { { 0, { CoreRootRef { CoreRootRef::Global, 0 } } } };
    touch.summary.reads = { CoreTarget { false, 0 } };

    m.funcs.push_back(wrap);
    m.funcs.push_back(touch);
    assert(Code(m) == "GIR-V050");
    m.funcs[1].summary.reads.push_back(CoreTarget { true, 0 });
    assert(Code(m) == "");
}

void RejectsParameterRootUnderapproximationAtCall() {
    auto m = Base();
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ref = m.RefType(CoreMut::Mut, i64);
    GirGlobal g;
    g.name = "counter";
    g.ty = i64;
    g.kind = CoreVarKind::Var;
    g.org = 0;
    g.init.name = "counter";
    g.init.results = { i64 };
    g.init.roots.results = { {} };
    g.init.summary.unknown = true;
    GirBlock init;
    init.insts = { Int(m, 0, "0"), Ret({ 0 }) };
    g.init.blocks = { init };
    m.globals.push_back(g);

    auto global = Def(GirOp::Global, 0);
    global.idx = 0;
    auto call = Def(GirOp::Call, 1);
    call.idx = 1;
    call.vals = { 0 };
    call.org = 0;
    Main(m).blocks[0].insts = { global, call, Ret() };
    Main(m).summary.reads = { CoreTarget { true, 0 } };

    GirFunc touch;
    touch.name = "touch";
    touch.params = { ref };
    touch.scopes = { -1 };
    GirBlock body;
    body.params = { { 0, ref } };
    auto load = Def(GirOp::Load, 1);
    load.a = 0;
    body.insts = { load, Ret() };
    touch.blocks = { body };
    touch.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    touch.summary.reads = { CoreTarget { false, 0 } };
    m.funcs.push_back(touch);

    assert(Code(m) == "GIR-V050");
}

void AcceptsUnreachableAfterANonReturningCall() {
    auto m = Base();
    auto call = Def(GirOp::Call, 0);
    call.idx = 1;
    call.org = 0;
    GirInst unreachable;
    unreachable.op = GirOp::Unreachable;
    Main(m).blocks[0].insts = { call, unreachable };
    Main(m).summary.aborts = true;

    GirFunc relay;
    relay.name = "relay";
    relay.scopes = { -1 };
    GirInst relayCall = Def(GirOp::Call, 0);
    relayCall.idx = 2;
    relayCall.org = 0;
    GirInst relayUnreachable;
    relayUnreachable.op = GirOp::Unreachable;
    GirBlock rb;
    rb.insts = { relayCall, relayUnreachable };
    relay.blocks = { rb };
    relay.summary.aborts = true;

    GirFunc stop;
    stop.name = "stop";
    stop.scopes = { -1 };
    GirInst exit;
    exit.op = GirOp::Exit;
    exit.a = 0;
    exit.org = 0;
    GirBlock b;
    b.insts = { Int(m, 0, "7"), exit };
    stop.blocks = { b };
    stop.summary.aborts = true;
    m.funcs.push_back(relay);
    m.funcs.push_back(stop);
    assert(Code(m) == "");
}

void RejectsUnreachableWithoutANonReturningCall() {
    auto m = Base();
    GirInst unreachable;
    unreachable.op = GirOp::Unreachable;
    Main(m).blocks[0].insts = { unreachable };
    assert(Code(m) == "GIR-V020");
}

void RejectsAbortingOperationWithoutOrigin() {
    auto m = Base();
    GirInst div = Def(GirOp::Bin, 2);
    div.bin = CoreBinOp::Div;
    div.ty = m.IntType(CoreIntTy::I64);
    div.a = 0;
    div.b = 1;
    div.org = -1;
    Main(m).blocks[0].insts = { Enter(0), Int(m, 0, "1"), Int(m, 1, "0"), div, Leave(0), Ret() };
    Main(m).summary.aborts = true;
    assert(Code(m) == "GIR-V100");
    Main(m).blocks[0].insts[3].org = 0;
    assert(Code(m) == "");
}

// A low module: one function, the entry, whose parameter is the stack base.
GirModule LowBase() {
    GirModule m;
    m.low = true;
    m.files = { "t.goose" };
    m.diagfiles = { "t.goose" };
    m.origins = { CoreOrigin { 0, 1, CoreOriginKind::Let } };
    auto i64 = m.IntType(CoreIntTy::I64);
    GirFunc f;
    f.name = "main";
    f.params = { i64 };
    f.scopes = { -1 };
    GirBlock b;
    b.params = { { 0, i64 } };
    b.insts = { Ret() };
    f.blocks = { b };
    f.summary.unknown = true;
    m.funcs = { f };
    return m;
}

void LowAccepts() {
    auto m = LowBase();
    assert(Code(m) == "");
    // A header on the function's own stack, marked and released.
    Main(m).stacks = 1;
    GirMember hdr;
    hdr.kind = GirMember::Header;
    hdr.stack = 0;
    hdr.scope = 0;
    Main(m).members = { hdr };
    GirInst at = Def(GirOp::StackAt, 1);
    at.a = 0;
    at.idx = 0;
    GirInst mark = Def(GirOp::StackMark, 2);
    mark.a = 1;
    GirInst release;
    release.op = GirOp::StackRelease;
    release.a = 1;
    release.b = 2;
    Main(m).blocks[0].insts = { at, mark, release, Ret() };
    assert(Code(m) == "");
}

void RejectsHighOperationInLowModule() {
    auto m = LowBase();
    GirInst snap = Def(GirOp::Snap, 1);
    snap.a = 0;
    Main(m).blocks[0].insts = { snap, Ret() };
    assert(Code(m) == "GIR-V090");
    // And a low operation in a high module.
    auto h = Base();
    GirInst frame = Def(GirOp::FrameAddr, 0);
    Main(h).blocks[0].insts = { frame, Ret() };
    assert(Code(h) == "GIR-V090");
}

void RejectsTwoResizablesOnOneStack() {
    auto m = LowBase();
    Main(m).stacks = 1;
    GirMember a, b;
    a.kind = b.kind = GirMember::Header;
    a.stack = b.stack = 0;
    a.scope = 0;
    b.scope = 0;
    Main(m).members = { a, b };
    assert(Code(m) == "GIR-V090");
    // Disjoint scopes may share it.
    Main(m).scopes = { -1, -1 };
    Main(m).members[1].scope = 1;
    assert(Code(m) == "");
}

void RejectsWatermarkPastCallerOwnedRegion() {
    auto m = LowBase();
    Main(m).stacks = 1;
    GirInst at = Def(GirOp::StackAt, 1);
    at.a = 0;
    at.idx = 3;   // Beyond the one stack the function owns: the caller's.
    GirInst mark = Def(GirOp::StackMark, 2);
    mark.a = 1;
    GirInst release;
    release.op = GirOp::StackRelease;
    release.a = 1;
    release.b = 2;
    Main(m).blocks[0].insts = { at, mark, release, Ret() };
    assert(Code(m) == "GIR-V090");
}

void RejectsUnresolvedLayout() {
    auto m = LowBase();
    GirFunc f = Main(m);
    f.name = "takes_slice";
    auto slice = m.SliceType(CoreMut::Mut, m.IntType(CoreIntTy::I64));
    f.params.push_back(slice);
    f.blocks[0].params.push_back({ 1, slice });
    m.funcs.push_back(f);
    assert(Code(m) == "GIR-V090");
}

void RejectsElementsThatDoNotTopTheirStack() {
    auto m = LowBase();
    Main(m).stacks = 1;
    GirMember hdr;
    hdr.kind = GirMember::Header;
    hdr.stack = 0;
    hdr.scope = 0;
    Main(m).members = { hdr };
    GirInst at = Def(GirOp::StackAt, 1);
    at.a = 0;
    at.idx = 0;
    GirInst frame = Def(GirOp::FrameAddr, 2);
    frame.idx = 0;
    GirInst mark = Def(GirOp::StackMark, 3);
    mark.a = 1;
    GirInst init;
    init.op = GirOp::HdrInit;
    init.a = 2;
    init.b = 3;
    GirInst bump;
    bump.op = GirOp::StackBump;
    bump.a = 1;
    bump.b = -1;
    bump.idx = 8;
    // A bump the length of the header does not follow.
    Main(m).blocks[0].insts = { at, frame, mark, init, bump, Ret() };
    assert(Code(m) == "GIR-V090");
    // With the length update it is the push the lowering writes.
    auto one = Int(m, 4, "1");
    GirInst setlen;
    setlen.op = GirOp::HdrSetLen;
    setlen.a = 2;
    setlen.b = 4;
    Main(m).blocks[0].insts = { at, frame, mark, init, bump, one, setlen, Ret() };
    assert(Code(m) == "");
    // A header started from a mark of another stack.
    Main(m).stacks = 2;
    GirInst at1 = Def(GirOp::StackAt, 3);
    at1.a = 0;
    at1.idx = 1;
    GirInst mark1 = Def(GirOp::StackMark, 4);
    mark1.a = 3;
    init.b = 4;
    Main(m).blocks[0].insts = { at, frame, at1, mark1, init, Ret() };
    assert(Code(m) == "GIR-V090");
}

GirTypeId StructType(GirModule &m, int sid) {
    CoreType t;
    t.kind = CoreType::Struct;
    t.structid = sid;
    return m.Intern(t);
}

GirModule ScalarStruct() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    m.diagfiles = { "t.goose" };
    auto u8 = m.IntType(CoreIntTy::U8);
    auto i64 = m.IntType(CoreIntTy::I64);
    m.structs = {
        CoreStruct { 9, {
            CoreField { u8, CoreVarKind::Var, CoreMut::Mut, 0 },
            CoreField { i64, CoreVarKind::Var, CoreMut::Mut, 1 },
        } },
        CoreStruct { 9, {
            CoreField { u8, CoreVarKind::Var, CoreMut::Mut, 0 },
            CoreField { i64, CoreVarKind::Var, CoreMut::Mut, 1 },
        } },
    };
    auto record = StructType(m, 0);
    (void)StructType(m, 1);
    Main(m).slots = { { record, CoreVarKind::Let, 0, 0 } };
    Main(m).summary.outputs = true;

    auto one = Int(m, 0, "5");
    one.ty = u8;
    auto two = Int(m, 1, "7");
    GirInst make = Def(GirOp::Struct, 2);
    make.ty = record;
    make.vals = { 0, 1 };
    GirInst init = Init(0, 2);
    GirInst owner = Def(GirOp::Slot, 3);
    owner.idx = 0;
    GirInst first = Def(GirOp::Field, 4);
    first.a = 3;
    first.idx = 0;
    auto replacement = Int(m, 5, "9");
    replacement.ty = u8;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 4;
    store.b = 5;
    store.org = 0;
    GirInst second = Def(GirOp::Field, 6);
    second.a = 3;
    second.idx = 1;
    GirInst read = Def(GirOp::Load, 7);
    read.a = 6;
    GirInst print;
    print.op = GirOp::Print;
    print.parts = { { false, "", 7 } };
    print.org = 0;
    Main(m).blocks[0].insts = {
        Enter(0), one, two, make, init, owner, first, replacement, store, second, read, print,
        Leave(0), Ret(),
    };
    return m;
}

void PilotAndShrinkModuleShapesStayDistinct() {
    CoreModule pilot;
    assert(CoreWriter(pilot).Write() ==
           "[\"module\",\"goose-core/0.2\",\"core-pilot\",[],[],[],[],[],0,[]]\n");
    pilot.profile = CoreProfile::Shrink;
    assert(CoreWriter(pilot).Write() ==
           "[\"module\",\"goose-core/0.2\",\"core-shrink\",[],[],[],[],[],[],0,[]]\n");
}

void AcceptsScalarStructFieldsOnAnImmutableBinding() {
    auto m = ScalarStruct();
    assert(Code(m) == "");
    auto json = GirWriter(m).Write();
    assert(json.find("\"core-shrink\"") != string::npos);
    assert(json.find("[\"struct_def\",9,") != string::npos);
    assert(json.find("[\"i_struct\"") != string::npos);
    assert(json.find("[\"i_field\"") != string::npos);
}

void RejectsStructsInThePilotProfile() {
    auto m = ScalarStruct();
    m.profile = CoreProfile::Pilot;
    assert(Code(m) == "GIR-V010");
}

void RejectsAStoreToALetField() {
    auto m = ScalarStruct();
    m.structs[0].fields[0].binding = CoreVarKind::Let;
    assert(Code(m) == "GIR-V030");
}

void RejectsAWriteThroughConstFieldContents() {
    auto m = ScalarStruct();
    auto u8 = m.IntType(CoreIntTy::U8);
    auto inner = StructType(m, 0);
    auto outer = StructType(m, 1);
    m.structs = {
        CoreStruct { 1, { CoreField { u8, CoreVarKind::Var, CoreMut::Mut, 0 } } },
        CoreStruct { 1, { CoreField { inner, CoreVarKind::Var, CoreMut::Const, 0 } } },
    };
    Main(m).slots[0].ty = outer;
    auto owner = Def(GirOp::Slot, 0);
    owner.idx = 0;
    auto innerfield = Def(GirOp::Field, 1);
    innerfield.a = 0;
    innerfield.idx = 0;
    auto scalarfield = Def(GirOp::Field, 2);
    scalarfield.a = 1;
    scalarfield.idx = 0;
    auto value = Int(m, 3, "9");
    value.ty = u8;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 2;
    store.b = 3;
    store.org = 0;
    Main(m).blocks[0].insts = { Enter(0), owner, innerfield, scalarfield, value, store, Leave(0), Ret() };
    assert(Code(m) == "GIR-V030");
}

void RejectsAConstructorWithAnotherNominalType() {
    auto m = ScalarStruct();
    auto wrong = StructType(m, 1);
    auto &insts = Main(m).blocks[0].insts;
    for (auto &i : insts)
        if (i.op == GirOp::Struct) i.ty = wrong;
    assert(Code(m) == "GIR-V010");

    auto count = ScalarStruct();
    for (auto &i : Main(count).blocks[0].insts)
        if (i.op == GirOp::Struct) i.vals.pop_back();
    assert(Code(count) == "GIR-V010");

    auto fieldType = ScalarStruct();
    for (auto &i : Main(fieldType).blocks[0].insts)
        if (i.op == GirOp::Struct) i.vals[0] = i.vals[1];
    assert(Code(fieldType) == "GIR-V010");

    auto fieldIndex = ScalarStruct();
    for (auto &i : Main(fieldIndex).blocks[0].insts)
        if (i.op == GirOp::Field) i.idx = 2;
    assert(Code(fieldIndex) == "GIR-V010");
}

void RejectsAFieldComponentAfterItsStructType() {
    auto m = ScalarStruct();
    auto record = Main(m).slots[0].ty;
    m.structs[0].fields[0].type = record;
    assert(Code(m) == "GIR-V010");
}

void RejectsAnInvalidStructLayout() {
    auto overlapping = ScalarStruct();
    overlapping.structs[0].fields[1].offset = 0;
    assert(Code(overlapping) == "GIR-V010");

    auto truncated = ScalarStruct();
    truncated.structs[0].size = 8;
    assert(Code(truncated) == "GIR-V010");
}

void LowStructUsesByteStorageAndUnalignedSafeAccess() {
    auto high = ScalarStruct();
    assert(Code(high) == "");
    auto low = GirToLow(high).Lower();
    assert(!GirVerifier(low).Verify());
    auto json = GirWriter(low).WriteLow();
    assert(json.find("\"core-shrink\"") != string::npos);
    assert(json.find("struct_def") == string::npos);
    auto byteCopies = 0;
    auto scalarLoads = 0;
    auto scalarStores = 0;
    unordered_map<int, string> integerValues;
    vector<string> copySizes;
    for (auto &block : low.funcs[0].blocks)
        for (auto &inst : block.insts) {
            byteCopies += inst.op == GirOp::BytesCopy;
            scalarLoads += inst.op == GirOp::PLoad;
            scalarStores += inst.op == GirOp::PStore;
            if (inst.op == GirOp::Int) integerValues[inst.res] = inst.text;
            if (inst.op == GirOp::BytesCopy) copySizes.push_back(integerValues[inst.vals[0]]);
        }
    assert(byteCopies >= 4);
    assert(scalarLoads == 0);
    assert(scalarStores == 0);
    assert((copySizes == vector<string>{ "1", "8", "9", "1", "8" }));
}

}  // namespace

int main() {
    Accepts();
    RejectsUseNotDominatedByDefinition();
    RejectsWrongEdgeArgumentType();
    RejectsBlockWithTwoTerminatorsOrNone();
    RejectsStoreThroughConst();
    RejectsSlotAddressOutsideItsScope();
    RejectsLoadOfResizable();
    RejectsUnbalancedScopesOnOnePath();
    RejectsReturnInsideAnEnteredScope();
    RejectsSummaryThatOmitsAWrite();
    RejectsCallThatPropagatesATarget();
    RejectsSummaryThatOmitsSliceParameterRebind();
    RejectsReferenceToSliceResult();
    RejectsReferenceToSliceGlobal();
    RejectsSummaryThatOmitsAGlobalReachedThroughACalleeParameter();
    RejectsParameterRootUnderapproximationAtCall();
    AcceptsUnreachableAfterANonReturningCall();
    RejectsUnreachableWithoutANonReturningCall();
    RejectsAbortingOperationWithoutOrigin();
    LowAccepts();
    RejectsHighOperationInLowModule();
    RejectsTwoResizablesOnOneStack();
    RejectsWatermarkPastCallerOwnedRegion();
    RejectsUnresolvedLayout();
    RejectsElementsThatDoNotTopTheirStack();
    PilotAndShrinkModuleShapesStayDistinct();
    AcceptsScalarStructFieldsOnAnImmutableBinding();
    RejectsStructsInThePilotProfile();
    RejectsAStoreToALetField();
    RejectsAWriteThroughConstFieldContents();
    RejectsAConstructorWithAnotherNominalType();
    RejectsAFieldComponentAfterItsStructType();
    RejectsAnInvalidStructLayout();
    LowStructUsesByteStorageAndUnalignedSafeAccess();
    puts("compiler_gir ok");
    return 0;
}
