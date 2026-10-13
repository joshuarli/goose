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
#include "../src/core/core_summary.h"
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

string Code(GirModule m);

CoreExprP CoreInt(CoreTypeId ty, const char *text) {
    auto expr = make_unique<CoreExpr>();
    expr->kind = CoreExprKind::Lit;
    expr->type = ty;
    expr->value = text;
    return expr;
}

CorePlaceP CoreLocal(int index) {
    auto place = make_unique<CorePlace>();
    place->kind = CorePlace::Local;
    place->index = index;
    return place;
}

CorePlaceP CoreFieldPlace(CorePlaceP base, int index) {
    auto place = make_unique<CorePlace>();
    place->kind = CorePlace::Field;
    place->base = std::move(base);
    place->index = index;
    return place;
}

CoreViewP CorePlaceView(CorePlaceP place) {
    auto view = make_unique<CoreView>();
    view->kind = CoreView::Of;
    view->place = std::move(place);
    return view;
}

CoreModule LetArrayFieldCase(bool byRefIteration, CoreMut contents = CoreMut::Mut) {
    CoreModule core;
    core.files = { "t.goose" };
    core.profile = CoreProfile::Shrink;
    auto i64 = core.IntType(CoreIntTy::I64);
    CoreType array;
    array.kind = CoreType::Arr;
    array.elem = i64;
    array.count = 1;
    auto arrayTy = core.Intern(array);
    CoreType record;
    record.kind = CoreType::Struct;
    record.structid = 0;
    auto recordTy = core.Intern(record);
    core.structs = { CoreStruct { 8, { CoreField { arrayTy, CoreVarKind::Let, contents, 0 } } } };
    CoreType ref;
    ref.kind = CoreType::Ref;
    ref.mut = CoreMut::Mut;
    ref.elem = i64;
    auto refI64 = core.Intern(ref);
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Let };
    CoreImpl impl;
    impl.name = "main";
    impl.summary.aborts = true;
    impl.vars = { CoreVar { "record", recordTy, CoreVarKind::Let, 0, origin } };
    impl.body.scope = 0;

    auto arrayValue = make_unique<CoreExpr>();
    arrayValue->kind = CoreExprKind::Arr;
    arrayValue->type = arrayTy;
    arrayValue->elems.push_back(CoreInt(i64, "1"));
    auto recordValue = make_unique<CoreExpr>();
    recordValue->kind = CoreExprKind::Struct;
    recordValue->type = recordTy;
    recordValue->elems.push_back(std::move(arrayValue));
    CoreStmt init;
    init.kind = CoreStmtKind::Let;
    init.var = 0;
    init.expr = std::move(recordValue);
    init.org = origin;
    impl.body.stmts.push_back(std::move(init));

    if (byRefIteration) {
        impl.vars.push_back(CoreVar { "element", refI64, CoreVarKind::Let, 1, origin });
        CoreStmt loop;
        loop.kind = CoreStmtKind::ForEach;
        loop.var = 1;
        loop.byRef = true;
        loop.view = CorePlaceView(CoreFieldPlace(CoreLocal(0), 0));
        loop.then = make_unique<CoreBlock>();
        loop.then->scope = 1;
        auto elementRef = make_unique<CoreExpr>();
        elementRef->kind = CoreExprKind::Read;
        elementRef->type = refI64;
        elementRef->place = CoreLocal(1);
        auto elementPlace = make_unique<CorePlace>();
        elementPlace->kind = CorePlace::Deref;
        elementPlace->expr = std::move(elementRef);
        CoreStmt write;
        write.kind = CoreStmtKind::Assign;
        write.place = std::move(elementPlace);
        write.expr = CoreInt(i64, "2");
        write.org = origin;
        loop.then->stmts.push_back(std::move(write));
        loop.org = origin;
        impl.body.stmts.push_back(std::move(loop));
    } else {
        auto element = make_unique<CorePlace>();
        element->kind = CorePlace::Elem;
        element->view = CorePlaceView(CoreFieldPlace(CoreLocal(0), 0));
        element->expr = CoreInt(i64, "0");
        element->org = origin;
        CoreStmt write;
        write.kind = CoreStmtKind::Assign;
        write.place = std::move(element);
        write.expr = CoreInt(i64, "2");
        write.org = origin;
        impl.body.stmts.push_back(std::move(write));
    }

    core.impls.push_back(std::move(impl));
    core.contexts = { CoreContext { .impl = 0 } };
    core.entry = 0;
    return core;
}

string CoreLoweringCode(const CoreModule &core) {
    auto gir = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Let } },
                          [](const CoreOrigin &) { return 0; }).Lower();
    return Code(std::move(gir));
}

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

void RejectsDuplicateVariablesForReferenceToSliceParameterSlots() {
    auto m = Base();
    auto slice = m.SliceType(CoreMut::Mut, m.IntType(CoreIntTy::I64));
    auto refSlice = m.RefType(CoreMut::Mut, slice);
    GirFunc f;
    f.name = "take_slice_reference";
    f.params = { refSlice };
    f.slots = { { refSlice, CoreVarKind::Let, 0, 0 }, { refSlice, CoreVarKind::Let, 0, 0 } };
    f.scopes = { -1 };
    GirBlock b;
    b.params = { { 0, refSlice } };
    b.insts = { Ret() };
    f.blocks = { b };
    m.funcs.push_back(f);
    assert(Code(m) == "GIR-V010");
}

void RejectsSlotVariableThatNamesAnotherReferenceToSliceParameter() {
    auto m = Base();
    auto slice = m.SliceType(CoreMut::Mut, m.IntType(CoreIntTy::I64));
    auto refSlice = m.RefType(CoreMut::Mut, slice);
    GirFunc f;
    f.name = "take_two_slice_references";
    f.params = { refSlice, refSlice };
    f.slots = { { refSlice, CoreVarKind::Let, 0, 1 } };
    f.scopes = { -1 };
    GirBlock b;
    b.params = { { 0, refSlice }, { 1, refSlice } };
    b.insts = { Ret() };
    f.blocks = { b };
    m.funcs.push_back(f);
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

GirModule LowPassedOwnerPairModule(bool unrelated, bool throughLocal, bool throughBlock) {
    auto m = LowBase();
    auto ptr = m.PtrType();
    Main(m).stacks = 2;
    GirMember first, second;
    first.kind = second.kind = GirMember::Header;
    first.stack = 0;
    second.stack = 1;
    first.scope = second.scope = 0;
    Main(m).members = { first, second };

    GirFunc consume;
    consume.name = "consume";
    consume.params = { m.IntType(CoreIntTy::I64), ptr, ptr, ptr, ptr };
    consume.scopes = { -1 };
    consume.summary.unknown = true;
    if (throughLocal) {
        GirMember headerLocal, stackLocal;
        headerLocal.kind = stackLocal.kind = GirMember::Scalar;
        headerLocal.ty = stackLocal.ty = ptr;
        headerLocal.scope = stackLocal.scope = 0;
        consume.members = { headerLocal, stackLocal };
    }
    GirBlock entry;
    entry.params = { { 0, m.IntType(CoreIntTy::I64) }, { 1, ptr }, { 2, ptr },
                     { 3, ptr }, { 4, ptr } };
    GirInst header, stack;
    if (throughLocal) {
        GirInst saveHeader, saveStack, loadHeader, loadStack;
        saveHeader.op = saveStack.op = GirOp::LocalSet;
        saveHeader.a = 1;
        saveHeader.idx = 0;
        saveStack.a = 2;
        saveStack.idx = 1;
        loadHeader = Def(GirOp::LocalGet, 5);
        loadHeader.idx = 0;
        loadStack = Def(GirOp::LocalGet, 6);
        loadStack.idx = 1;
        header = Def(GirOp::HdrBase, 7);
        header.a = 5;
        stack.op = GirOp::StackRelease;
        stack.a = unrelated ? 4 : 6;
        stack.b = 7;
        entry.insts = { saveHeader, saveStack, loadHeader, loadStack, header, stack, Ret() };
    } else if (throughBlock) {
        GirInst branch;
        branch.op = GirOp::Br;
        branch.idx = 1;
        branch.vals = { 1, 2 };
        entry.insts = { branch };
        GirBlock body;
        body.params = { { 5, ptr }, { 6, ptr } };
        header = Def(GirOp::HdrBase, 7);
        header.a = 5;
        stack.op = GirOp::StackRelease;
        stack.a = unrelated ? 4 : 6;
        stack.b = 7;
        body.insts = { header, stack, Ret() };
        consume.blocks = { entry, body };
    } else {
        header = Def(GirOp::HdrBase, 5);
        header.a = 1;
        stack.op = GirOp::StackRelease;
        stack.a = unrelated ? 4 : 2;
        stack.b = 5;
        entry.insts = { header, stack, Ret() };
    }
    if (consume.blocks.empty()) consume.blocks = { entry };
    m.funcs.push_back(std::move(consume));

    GirInst firstHeader = Def(GirOp::FrameAddr, 1);
    firstHeader.idx = 0;
    GirInst firstStack = Def(GirOp::StackAt, 2);
    firstStack.a = 0;
    firstStack.idx = 0;
    GirInst secondHeader = Def(GirOp::FrameAddr, 3);
    secondHeader.idx = 1;
    GirInst secondStack = Def(GirOp::StackAt, 4);
    secondStack.a = 0;
    secondStack.idx = 1;
    GirInst call;
    call.op = GirOp::Call;
    call.idx = 1;
    call.vals = { 0, 1, 2, 3, 4 };
    call.org = 0;
    Main(m).blocks[0].insts = { firstHeader, firstStack, secondHeader, secondStack, call, Ret() };
    return m;
}

void PassedOwnerPairsKeepTheirExactIdentity() {
    assert(Code(LowPassedOwnerPairModule(true, false, false)) == "GIR-V090");
    assert(Code(LowPassedOwnerPairModule(false, false, false)) == "");
    assert(Code(LowPassedOwnerPairModule(false, true, false)) == "");
    assert(Code(LowPassedOwnerPairModule(false, false, true)) == "");
}

GirModule ShrinkReplaceBindingModule(bool throughPhi, bool throughCall) {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::GrowShrink;
    owner.elem = i64;
    auto ownerTy = m.Intern(owner);
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    Main(m).slots = { { ownerTy, CoreVarKind::Let, 0, 0 } };
    Main(m).summary.unknown = true;

    if (throughCall) {
        GirInst empty = Def(GirOp::Arr, 0);
        empty.ty = ownerTy;
        auto slot = Def(GirOp::Slot, 1);
        slot.idx = 0;
        auto call = Def(GirOp::Call, 2);
        call.idx = 1;
        call.vals = { 1 };
        call.org = 0;
        Main(m).blocks[0].insts = { Enter(0), empty, Init(0, 0), slot, call, Leave(0), Ret() };

        GirFunc replacement;
        replacement.name = "replace";
        replacement.params = { refTy };
        replacement.scopes = { -1 };
        replacement.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
        replacement.summary.unknown = true;
        GirBlock body;
        body.params = { { 0, refTy } };
        GirInst clear;
        clear.op = GirOp::Clear;
        clear.a = 0;
        clear.org = 0;
        auto value = Int(m, 1, "7");
        auto run = Def(GirOp::Arr, 2);
        run.ty = ownerTy;
        run.vals = { 1 };
        GirInst replace;
        replace.op = GirOp::Replace;
        replace.a = 0;
        replace.b = 2;
        replace.org = 0;
        body.insts = { clear, value, run, replace, Ret() };
        replacement.blocks = { body };
        m.funcs.push_back(std::move(replacement));
        return m;
    }

    GirInst empty = Def(GirOp::Arr, 0);
    empty.ty = ownerTy;
    auto slot = Def(GirOp::Slot, 1);
    slot.idx = 0;
    GirBlock entry;
    if (throughPhi) {
        auto cond = Def(GirOp::Bool, 2);
        cond.flag = true;
        entry.insts = { Enter(0), empty, Init(0, 0), slot, cond, CondBr(2, 1, 2) };
        GirBlock left, right, join;
        left.insts = { Br(3, { 1 }) };
        right.insts = { Br(3, { 1 }) };
        join.params = { { 3, refTy } };
        GirInst clear;
        clear.op = GirOp::Clear;
        clear.a = 3;
        clear.org = 0;
        auto value = Int(m, 4, "7");
        auto run = Def(GirOp::Arr, 5);
        run.ty = ownerTy;
        run.vals = { 4 };
        GirInst replace;
        replace.op = GirOp::Replace;
        replace.a = 3;
        replace.b = 5;
        replace.org = 0;
        join.insts = { clear, value, run, replace, Leave(0), Ret() };
        Main(m).blocks = { entry, left, right, join };
    } else {
        slot.res = 1;
        Main(m).blocks[0].insts = { Enter(0), empty, Init(0, 0), slot, Leave(0), Ret() };
    }
    return m;
}

void RejectsReplacementThroughALetOwnerPhi() {
    assert(Code(ShrinkReplaceBindingModule(true, false)) == "GIR-V030");
    assert(Code(ShrinkReplaceBindingModule(false, true)) == "");
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
    auto replacementWide = Int(m, 8, "11");
    GirInst storeWide;
    storeWide.op = GirOp::Store;
    storeWide.a = 6;
    storeWide.b = 8;
    storeWide.org = 0;
    GirInst read = Def(GirOp::Load, 7);
    read.a = 6;
    GirInst print;
    print.op = GirOp::Print;
    print.parts = { { false, "", 7 } };
    print.org = 0;
    Main(m).blocks[0].insts = {
        Enter(0), one, two, make, init, owner, first, replacement, store, second, replacementWide,
        storeWide, read, print,
        Leave(0), Ret(),
    };
    return m;
}

void PilotAndShrinkModuleShapesStayDistinct() {
    CoreModule pilot;
    assert(CoreWriter(pilot).Write() ==
           "[\"module\",\"goose-core/0.2\",\"core-pilot\",[],[],[],[],[],0,[]]\n");
    auto highPilot = Base();
    assert(GirWriter(highPilot).Write().find("[\"summary\",[],[],[],[],0,0]") != string::npos);
    highPilot.profile = CoreProfile::Shrink;
    assert(GirWriter(highPilot).Write().find("[\"summary\",[],[],[],[],[],0,0]") != string::npos);
    pilot.profile = CoreProfile::Shrink;
    assert(CoreWriter(pilot).Write() ==
           "[\"module\",\"goose-core/0.2\",\"core-shrink\",[],[],[],[],[],[],0,[]]\n");
}

CoreModule CorePushShape(CoreProfile profile) {
    CoreModule m;
    m.files = { "t.goose" };
    m.profile = profile;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::Grow;
    owner.elem = i64;
    auto ownerTy = m.Intern(owner);

    CoreImpl impl;
    impl.name = "main";
    impl.vars = { CoreVar { "values", ownerTy, CoreVarKind::Var, 0,
                            CoreOrigin { 0, 1, CoreOriginKind::Let } } };
    impl.body.scope = 0;
    auto push = make_unique<CoreExpr>();
    push->kind = CoreExprKind::Push;
    push->type = i64;
    push->place = CoreLocal(0);
    push->a = CoreInt(i64, "1");
    push->org = CoreOrigin { 0, 2, CoreOriginKind::Expr };
    CoreStmt stmt;
    stmt.kind = CoreStmtKind::Expr;
    stmt.expr = std::move(push);
    stmt.org = CoreOrigin { 0, 2, CoreOriginKind::Expr };
    impl.body.stmts.push_back(std::move(stmt));
    CoreStmt append;
    append.kind = CoreStmtKind::Append;
    append.place = CoreLocal(0);
    append.view = CorePlaceView(CoreLocal(0));
    append.org = CoreOrigin { 0, 3, CoreOriginKind::Expr };
    impl.body.stmts.push_back(std::move(append));
    impl.summary.grows = { CoreTarget { false, 0 } };
    impl.summary.shrinks = { CoreTarget { false, 0 } };
    m.impls.push_back(std::move(impl));
    m.entry = 0;
    return m;
}

CoreModule CorePushParamSummary(CoreProfile profile) {
    CoreModule m;
    m.files = { "t.goose" };
    m.profile = profile;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::Grow;
    owner.elem = i64;
    auto ownerTy = m.Intern(owner);
    CoreType ref;
    ref.kind = CoreType::Ref;
    ref.mut = CoreMut::Mut;
    ref.elem = ownerTy;
    auto refTy = m.Intern(ref);

    CoreImpl impl;
    impl.name = "push";
    impl.params = { CoreParam { 0, true } };
    impl.vars = { CoreVar { "values", refTy, CoreVarKind::Let, 0,
                            CoreOrigin { 0, 1, CoreOriginKind::Param } } };
    impl.body.scope = 0;
    auto read = make_unique<CoreExpr>();
    read->kind = CoreExprKind::Read;
    read->type = refTy;
    read->place = CoreLocal(0);
    auto ownerPlace = make_unique<CorePlace>();
    ownerPlace->kind = CorePlace::Deref;
    ownerPlace->expr = std::move(read);
    auto push = make_unique<CoreExpr>();
    push->kind = CoreExprKind::Push;
    push->type = i64;
    push->place = std::move(ownerPlace);
    push->a = CoreInt(i64, "1");
    push->org = CoreOrigin { 0, 2, CoreOriginKind::Expr };
    CoreStmt stmt;
    stmt.kind = CoreStmtKind::Expr;
    stmt.expr = std::move(push);
    stmt.org = CoreOrigin { 0, 2, CoreOriginKind::Expr };
    impl.body.stmts.push_back(std::move(stmt));
    m.impls.push_back(std::move(impl));
    CoreContext context;
    context.impl = 0;
    context.declkey = "push";
    context.varroots = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    m.contexts.push_back(std::move(context));
    m.entry = 0;
    return m;
}

void CoreShrinkPushAndSummaryCarryOriginsAndShrinks() {
    auto shrink = CoreWriter(CorePushShape(CoreProfile::Shrink)).Write();
    assert(shrink.find("[\"grow\",0]") != string::npos);
    assert(shrink.find("[\"e_push\",[\"p_local\",0],[\"e_lit\",0,\"1\"],1]") != string::npos);
    assert(shrink.find("[\"s_append\",[\"p_local\",0],[\"v_of\",[\"p_local\",0]],2]") !=
           string::npos);
    assert(shrink.find("[\"summary\",[],[],[[\"t_param\",0]],[[\"t_param\",0]],[],0,0]") !=
           string::npos);
    assert(shrink.find("[\"origin\",0,2,\"expr\"]") != string::npos);

    auto pilot = CoreWriter(CorePushShape(CoreProfile::Pilot)).Write();
    assert(pilot.find("[\"grow\",0]") != string::npos);
    assert(pilot.find("[\"e_push\",[\"p_local\",0],[\"e_lit\",0,\"1\"]]") != string::npos);
    assert(pilot.find("[\"s_append\",[\"p_local\",0],[\"v_of\",[\"p_local\",0]],2]") !=
           string::npos);
    assert(pilot.find("[[\"t_param\",0]],[],0,0]") != string::npos);

    auto pilotSummary = CorePushParamSummary(CoreProfile::Pilot);
    CoreSummarizer(pilotSummary).Run();
    auto pilotSummaryWire = CoreWriter(pilotSummary).Write();
    assert(pilotSummaryWire.find("[\"summary\",[],[],[[\"t_param\",0]],[],0,0]") !=
           string::npos);

    auto shrinkSummary = CorePushParamSummary(CoreProfile::Shrink);
    CoreSummarizer(shrinkSummary).Run();
    auto shrinkSummaryWire = CoreWriter(shrinkSummary).Write();
    assert(shrinkSummaryWire.find(
               "[\"summary\",[],[[\"t_param\",0]],[[\"t_param\",0]],[],[],0,0]") !=
           string::npos);
}

CoreModule CoreShrinkOperations() {
    CoreModule m;
    m.files = { "t.goose" };
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::GrowShrink;
    owner.elem = i64;
    auto ownerTy = m.Intern(owner);
    CoreImpl impl;
    impl.name = "main";
    impl.vars = { CoreVar { "values", ownerTy, CoreVarKind::Var, 0,
                            CoreOrigin { 0, 1, CoreOriginKind::Let } } };
    impl.body.scope = 0;

    auto pop = make_unique<CoreExpr>();
    pop->kind = CoreExprKind::Pop;
    pop->type = i64;
    pop->place = CoreLocal(0);
    pop->org = CoreOrigin { 0, 2, CoreOriginKind::Expr };
    CoreStmt popStmt;
    popStmt.kind = CoreStmtKind::Expr;
    popStmt.expr = std::move(pop);
    popStmt.org = CoreOrigin { 0, 2, CoreOriginKind::Expr };
    impl.body.stmts.push_back(std::move(popStmt));

    CoreStmt popn;
    popn.kind = CoreStmtKind::PopN;
    popn.place = CoreLocal(0);
    popn.expr = CoreInt(i64, "1");
    popn.org = CoreOrigin { 0, 3, CoreOriginKind::Expr };
    impl.body.stmts.push_back(std::move(popn));

    CoreStmt resize;
    resize.kind = CoreStmtKind::Resize;
    resize.place = CoreLocal(0);
    resize.expr = CoreInt(i64, "2");
    resize.expr2 = CoreInt(i64, "40");
    resize.org = CoreOrigin { 0, 4, CoreOriginKind::Expr };
    impl.body.stmts.push_back(std::move(resize));

    CoreStmt clear;
    clear.kind = CoreStmtKind::Clear;
    clear.place = CoreLocal(0);
    clear.org = CoreOrigin { 0, 5, CoreOriginKind::Expr };
    impl.body.stmts.push_back(std::move(clear));

    auto replacement = make_unique<CoreExpr>();
    replacement->kind = CoreExprKind::Arr;
    replacement->type = ownerTy;
    replacement->elems.push_back(CoreInt(i64, "7"));
    CoreStmt assign;
    assign.kind = CoreStmtKind::AssignWhole;
    assign.place = CoreLocal(0);
    assign.expr = std::move(replacement);
    assign.org = CoreOrigin { 0, 6, CoreOriginKind::Assign };
    impl.body.stmts.push_back(std::move(assign));

    m.impls.push_back(std::move(impl));
    m.contexts = { CoreContext { .impl = 0 } };
    m.entry = 0;
    return m;
}

void CoreShrinkOperationTagsAndPlaceTypingAreCanonical() {
    auto m = CoreShrinkOperations();
    auto json = CoreWriter(m).Write();
    assert(json.find("[\"growshrink\",0]") != string::npos);
    assert(json.find("[\"e_pop\",[\"p_local\",0],1]") != string::npos);
    assert(json.find("[\"s_pop_n\",[\"p_local\",0],[\"e_lit\",0,\"1\"],2]") !=
           string::npos);
    assert(json.find("[\"s_resize\",[\"p_local\",0],[\"e_lit\",0,\"2\"],[[\"e_lit\",0,\"40\"]],3]") !=
           string::npos);
    assert(json.find("[\"s_clear\",[\"p_local\",0],4]") != string::npos);
    assert(json.find("[\"s_assign_whole\",[\"p_local\",0],[\"e_arr\",1,[") !=
           string::npos);
    CoreSummarizer(m).Run();
    assert(m.impls[0].summary.aborts);
    assert(CoreWriter(m).Write().find("[\"summary\",[],[],[],[],[],1,0]") != string::npos);

    auto limited = CorePushShape(CoreProfile::Shrink);
    CoreType bounded;
    bounded.kind = CoreType::Limited;
    bounded.elem = limited.IntType(CoreIntTy::I64);
    bounded.count = 3;
    auto boundedTy = limited.Intern(bounded);
    limited.impls[0].vars[0].type = boundedTy;
    auto &push = *limited.impls[0].body.stmts[0].expr;
    auto actual = limited.PlaceType(0, *push.place);
    assert(actual && *actual == boundedTy);
    CoreSummarizer(limited).Run();
    assert(limited.impls[0].summary.aborts);
}

void CoreShrinkOperationsLowerToVerifiedGir() {
    auto core = CoreShrinkOperations();
    CoreSummarizer(core).Run();
    auto high = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Expr } },
                           [](const CoreOrigin &) { return 0; }).Lower();
    assert(Code(high) == "");
    auto json = GirWriter(high).Write();
    for (auto tag : { "growshrink", "i_pop", "x_pop_n", "x_resize", "x_clear", "x_replace" })
        assert(json.find(tag) != string::npos);
    assert(json.find("[\"summary\",[],[],[],[],[],1,0]") != string::npos);
    auto clearAt = -1, replaceAt = -1, replacementAt = -1;
    for (auto &block : high.funcs[0].blocks)
        for (size_t k = 0; k < block.insts.size(); k++) {
            auto &inst = block.insts[k];
            if (inst.op == GirOp::Clear) clearAt = (int)k;
            if (inst.op == GirOp::Arr) replacementAt = (int)k;
            if (inst.op == GirOp::Replace) replaceAt = (int)k;
        }
    assert(clearAt >= 0 && replacementAt > clearAt && replaceAt > replacementAt);
    auto low = GirToLow(high).Lower();
    if (auto violation = GirVerifier(low).Verify())
        fprintf(stderr, "%s: %s\n", violation->code.c_str(), violation->message.c_str());
    assert(!GirVerifier(low).Verify());
    auto popEmpty = 0, popNRange = 0, resizeNegative = 0, resizeFill = 0;
    for (auto &type : low.types)
        assert(type.kind != CoreType::GrowShrink && type.kind != CoreType::Limited);
    for (auto &function : low.funcs)
        for (auto &block : function.blocks)
            for (auto &inst : block.insts)
                if (inst.op == GirOp::Abort) {
                    popEmpty += inst.abort == GirAbortKind::PopEmpty;
                    popNRange += inst.abort == GirAbortKind::PopNRange;
                    resizeNegative += inst.abort == GirAbortKind::ResizeNegative;
                    resizeFill += inst.abort == GirAbortKind::ResizeFill;
                }
    assert(popEmpty == 1 && popNRange == 1 && resizeNegative == 1 && resizeFill == 0);
}

GirModule ShrinkResizeModule(CoreType::Kind ownerKind, bool fillCall) {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = ownerKind;
    owner.elem = i64;
    if (ownerKind == CoreType::Limited) owner.count = 2;
    auto ownerTy = m.Intern(owner);
    auto ref = m.RefType(CoreMut::Mut, ownerTy);

    GirFunc resize;
    resize.name = "resize";
    resize.params = { ref, i64 };
    resize.scopes = { -1 };
    resize.summary.unknown = true;
    GirBlock body;
    body.params = { { 0, ref }, { 1, i64 } };
    int fill = -1;
    if (fillCall) {
        fill = 2;
        auto call = Def(GirOp::Call, fill);
        call.idx = 2;
        call.org = 0;
        body.insts.push_back(call);
    }
    GirInst resizeInst;
    resizeInst.op = GirOp::Resize;
    resizeInst.a = 0;
    resizeInst.b = 1;
    if (fillCall) resizeInst.vals = { fill };
    resizeInst.org = 0;
    body.insts.push_back(resizeInst);
    body.insts.push_back(Ret());
    resize.blocks = { body };
    m.funcs.push_back(std::move(resize));

    if (fillCall) {
        GirFunc fillFunction;
        fillFunction.name = "fill";
        fillFunction.results = { i64 };
        fillFunction.scopes = { -1 };
        fillFunction.summary.unknown = true;
        GirBlock fillBody;
        auto value = Int(m, 0, "7");
        fillBody.insts = { value, Ret({ 0 }) };
        fillFunction.blocks = { fillBody };
        m.funcs.push_back(std::move(fillFunction));
    }
    return m;
}

vector<GirAbortKind> BranchFailureKinds(const GirFunc &function) {
    vector<GirAbortKind> out;
    for (auto &block : function.blocks) {
        if (block.insts.empty() || block.insts.back().op != GirOp::CondBr) continue;
        auto fail = block.insts.back().idx2;
        if (fail < 0 || fail >= (int)function.blocks.size()) continue;
        auto &target = function.blocks[fail];
        if (!target.insts.empty() && target.insts.back().op == GirOp::Abort)
            out.push_back(target.insts.back().abort);
    }
    return out;
}

void ResizeChecksFollowNegativeSizeAndEvaluateFillFirst() {
    auto limited = ShrinkResizeModule(CoreType::Limited, true);
    assert(Code(limited) == "");
    auto &high = limited.funcs[1].blocks[0].insts;
    auto callAt = -1, resizeAt = -1;
    for (size_t k = 0; k < high.size(); k++) {
        if (high[k].op == GirOp::Call) callAt = (int)k;
        if (high[k].op == GirOp::Resize) resizeAt = (int)k;
    }
    assert(callAt >= 0 && resizeAt > callAt);

    auto low = GirToLow(limited).Lower();
    assert(!GirVerifier(low).Verify());
    auto checks = BranchFailureKinds(low.funcs[1]);
    assert(checks.size() >= 2 && checks[0] == GirAbortKind::ResizeNegative &&
           checks[1] == GirAbortKind::Capacity);
    pair<int, int> callPosition { -1, -1 }, firstCheckPosition { -1, -1 };
    for (size_t b = 0; b < low.funcs[1].blocks.size(); b++)
        for (size_t k = 0; k < low.funcs[1].blocks[b].insts.size(); k++) {
            auto &inst = low.funcs[1].blocks[b].insts[k];
            if (inst.op == GirOp::Call) callPosition = { (int)b, (int)k };
            if (inst.op == GirOp::CondBr && firstCheckPosition.first < 0)
                firstCheckPosition = { (int)b, (int)k };
        }
    assert(callPosition.first >= 0 && firstCheckPosition.first >= callPosition.first &&
           (firstCheckPosition.first != callPosition.first || firstCheckPosition.second > callPosition.second));

    auto noFill = ShrinkResizeModule(CoreType::GrowShrink, false);
    assert(Code(noFill) == "");
    auto noFillLow = GirToLow(noFill).Lower();
    assert(!GirVerifier(noFillLow).Verify());
    auto noFillChecks = BranchFailureKinds(noFillLow.funcs[1]);
    assert(noFillChecks.size() >= 2 && noFillChecks[0] == GirAbortKind::ResizeNegative &&
           noFillChecks[1] == GirAbortKind::ResizeFill);
}

GirModule LimitedAppendModule() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::Limited;
    owner.elem = i64;
    owner.count = 1;
    auto ownerTy = m.Intern(owner);
    auto ref = m.RefType(CoreMut::Mut, ownerTy);
    auto view = m.SliceType(CoreMut::Mut, i64);
    GirFunc append;
    append.name = "append";
    append.params = { ref, view };
    append.scopes = { -1 };
    append.summary.unknown = true;
    GirBlock body;
    body.params = { { 0, ref }, { 1, view } };
    auto viewValue = Def(GirOp::SliceView, 2);
    viewValue.a = 1;
    GirInst instruction;
    instruction.op = GirOp::Append;
    instruction.a = 0;
    instruction.b = 2;
    instruction.org = 0;
    body.insts = { viewValue, instruction, Ret() };
    append.blocks = { body };
    m.funcs.push_back(std::move(append));
    return m;
}

void LimitedAppendChecksCapacityBeforeWriting() {
    auto high = LimitedAppendModule();
    auto highCode = Code(high);
    if (auto violation = GirVerifier(high).Verify())
        fprintf(stderr, "limited append GIR: %s: %s\n", violation->code.c_str(), violation->message.c_str());
    assert(highCode == "");
    auto low = GirToLow(high).Lower();
    assert(!GirVerifier(low).Verify());
    bool checkedBeforeWrite = false;
    for (auto &block : low.funcs[1].blocks) {
        if (block.insts.empty() || block.insts.back().op != GirOp::CondBr) continue;
        auto &branch = block.insts.back();
        if (branch.idx2 < 0 || branch.idx2 >= (int)low.funcs[1].blocks.size()) continue;
        auto &fail = low.funcs[1].blocks[branch.idx2];
        if (fail.insts.empty() || fail.insts.back().op != GirOp::Abort ||
            fail.insts.back().abort != GirAbortKind::Capacity) continue;
        auto &success = low.funcs[1].blocks[branch.idx];
        assert(find_if(block.insts.begin(), block.insts.end(),
                       [](auto &i) { return i.op == GirOp::BytesMove; }) == block.insts.end());
        checkedBeforeWrite = find_if(success.insts.begin(), success.insts.end(),
                                     [](auto &i) { return i.op == GirOp::BytesMove; }) !=
                             success.insts.end();
    }
    assert(checkedBeforeWrite);
}

void AggregatePopCopiesBeforeReleasingItsStack() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType record;
    record.kind = CoreType::Struct;
    record.structid = 0;
    auto recordTy = m.Intern(record);
    m.structs = { CoreStruct { 8, { CoreField { i64, CoreVarKind::Var, CoreMut::Mut, 0 } } } };
    CoreType owner;
    owner.kind = CoreType::GrowShrink;
    owner.elem = recordTy;
    auto ownerTy = m.Intern(owner);
    auto ref = m.RefType(CoreMut::Mut, ownerTy);
    GirFunc pop;
    pop.name = "pop_record";
    pop.params = { ref };
    pop.scopes = { -1 };
    pop.summary.unknown = true;
    GirBlock body;
    body.params = { { 0, ref } };
    auto operation = Def(GirOp::Pop, 1);
    operation.a = 0;
    operation.org = 0;
    body.insts = { operation, Ret() };
    pop.blocks = { body };
    m.funcs.push_back(std::move(pop));
    assert(Code(m) == "");

    auto low = GirToLow(m).Lower();
    assert(!GirVerifier(low).Verify());
    bool copiedFirst = false;
    for (auto &block : low.funcs[1].blocks) {
        auto copy = find_if(block.insts.begin(), block.insts.end(),
                            [](auto &i) { return i.op == GirOp::BytesCopy; });
        auto release = find_if(block.insts.begin(), block.insts.end(),
                               [](auto &i) { return i.op == GirOp::StackRelease; });
        if (copy != block.insts.end() && release != block.insts.end())
            copiedFirst = copy < release;
    }
    assert(copiedFirst);
}

void LimitedClearStoresItsLengthInByteStorage() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType limited;
    limited.kind = CoreType::Limited;
    limited.elem = i64;
    limited.count = 256;
    auto owner = m.Intern(limited);
    auto ref = m.RefType(CoreMut::Mut, owner);
    GirFunc function;
    function.name = "clear_limited";
    function.params = { ref };
    function.scopes = { -1 };
    function.summary.unknown = true;
    GirBlock body;
    body.params = { { 0, ref } };
    GirInst clear;
    clear.op = GirOp::Clear;
    clear.a = 0;
    clear.org = 0;
    body.insts = { clear, Ret() };
    function.blocks = { body };
    m.funcs.push_back(std::move(function));

    assert(Code(m) == "");
    auto low = GirToLow(m).Lower();
    assert(!GirVerifier(low).Verify());
    auto byteCopies = 0;
    for (auto &block : low.funcs[1].blocks)
        for (auto &inst : block.insts)
            byteCopies += inst.op == GirOp::BytesCopy;
    assert(byteCopies == 1);
}

GirModule LetOwnerPush(CoreProfile profile, CoreType::Kind ownerKind) {
    auto m = Base();
    m.profile = profile;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = ownerKind;
    owner.elem = i64;
    if (ownerKind == CoreType::Limited) owner.count = 2;
    auto ownerTy = m.Intern(owner);
    Main(m).slots = { { ownerTy, CoreVarKind::Let, 0, 0 } };
    Main(m).summary.unknown = true;

    auto empty = Def(GirOp::Arr, 0);
    empty.ty = ownerTy;
    auto init = Init(0, 0);
    auto slot = Def(GirOp::Slot, 1);
    slot.idx = 0;
    auto value = Int(m, 2, "1");
    auto push = Def(GirOp::Push, 3);
    push.a = 1;
    push.b = 2;
    push.org = 0;
    Main(m).blocks[0].insts = { Enter(0), empty, init, slot, value, push, Leave(0), Ret() };
    return m;
}

GirModule ShrinkSummaryModule() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::GrowShrink;
    owner.elem = i64;
    auto ownerTy = m.Intern(owner);
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);

    GirFunc pop;
    pop.name = "pop";
    pop.params = { refTy };
    pop.scopes = { -1 };
    pop.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    pop.summary.reads = { CoreTarget { false, 0 } };
    pop.summary.shrinks = { CoreTarget { false, 0 } };
    pop.summary.aborts = true;
    GirBlock body;
    body.params = { { 0, refTy } };
    auto instruction = Def(GirOp::Pop, 1);
    instruction.a = 0;
    instruction.org = 0;
    body.insts = { instruction, Ret() };
    pop.blocks = { body };
    m.funcs.push_back(std::move(pop));
    return m;
}

GirModule AppendSummaryModule() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::GrowShrink;
    owner.elem = i64;
    auto ownerTy = m.Intern(owner);
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    auto sliceTy = m.SliceType(CoreMut::Mut, i64);

    GirFunc append;
    append.name = "append";
    append.params = { refTy, sliceTy };
    append.scopes = { -1 };
    append.roots.params = {
        { 0, { CoreRootRef { CoreRootRef::Param, 0 } } },
        { 1, { CoreRootRef { CoreRootRef::Param, 1 } } },
    };
    append.summary.reads = { CoreTarget { false, 1 } };
    append.summary.writes = { CoreTarget { false, 0 } };
    append.summary.grows = { CoreTarget { false, 0 } };
    GirBlock body;
    body.params = { { 0, refTy }, { 1, sliceTy } };
    auto view = Def(GirOp::SliceView, 2);
    view.a = 1;
    GirInst instruction;
    instruction.op = GirOp::Append;
    instruction.a = 0;
    instruction.b = 2;
    instruction.org = 0;
    body.insts = { view, instruction, Ret() };
    append.blocks = { body };
    m.funcs.push_back(std::move(append));
    return m;
}

void ShrinkSummariesSerializeAndCoverPopEffects() {
    auto m = ShrinkSummaryModule();
    assert(Code(m) == "");
    auto json = GirWriter(m).Write();
    assert(json.find("[\"summary\",[[\"t_param\",0]],[],[],[[\"t_param\",0]],[],1,0]") !=
           string::npos);
    m.funcs[1].summary.shrinks.clear();
    assert(Code(m) == "GIR-V050");
}

void AppendSummaryIncludesItsViewSourceRead() {
    auto m = AppendSummaryModule();
    assert(Code(m) == "");
    m.funcs[1].summary.reads.clear();
    assert(Code(m) == "GIR-V050");
}

void PilotLetGrowPushUsesContentsPermission() {
    auto m = LetOwnerPush(CoreProfile::Pilot, CoreType::Grow);
    assert(Code(m) == "");
}

void LetLimitedOwnerSupportsDirectPushPopAndClear() {
    auto m = LetOwnerPush(CoreProfile::Shrink, CoreType::Limited);
    Main(m).summary.unknown = true;
    auto &insts = Main(m).blocks[0].insts;
    auto slot = Def(GirOp::Slot, 4);
    slot.idx = 0;
    auto pop = Def(GirOp::Pop, 5);
    pop.a = 4;
    pop.org = 0;
    auto slotAgain = Def(GirOp::Slot, 6);
    slotAgain.idx = 0;
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 6;
    clear.org = 0;
    insts.insert(insts.end() - 2, { slot, pop, slotAgain, clear });
    assert(Code(m) == "");
}

void RejectsPassingALetLimitedOwnerAsAMutableReference() {
    auto m = LetOwnerPush(CoreProfile::Shrink, CoreType::Limited);
    auto refTy = m.RefType(CoreMut::Mut, Main(m).slots[0].ty);
    GirFunc mutate;
    mutate.name = "mutate_limited";
    mutate.params = { refTy };
    mutate.scopes = { -1 };
    GirBlock callee;
    callee.params = { { 0, refTy } };
    callee.insts = { Ret() };
    mutate.blocks = { callee };
    m.funcs.push_back(std::move(mutate));

    auto &insts = Main(m).blocks[0].insts;
    auto slot = Def(GirOp::Slot, 4);
    slot.idx = 0;
    GirInst call;
    call.op = GirOp::Call;
    call.idx = 1;
    call.vals = { 4 };
    call.org = 0;
    insts.insert(insts.end() - 2, { slot, call });
    assert(Code(m) == "GIR-V010");
}

void ShrinkOperationsAndAbortTagsStayOutOfPilotGir() {
    auto operation = Base();
    operation.profile = CoreProfile::Pilot;
    auto pop = Def(GirOp::PopN, -1);
    Main(operation).blocks[0].insts = { pop, Ret() };
    assert(Code(operation) == "GIR-V010");

    auto abort = Base();
    abort.low = true;
    GirInst trap;
    trap.op = GirOp::Abort;
    trap.abort = GirAbortKind::PopEmpty;
    trap.org = 0;
    Main(abort).blocks[0].insts = { trap };
    assert(Code(abort) == "GIR-V010");

    auto highAbort = Base();
    highAbort.profile = CoreProfile::Shrink;
    Main(highAbort).blocks[0].insts = { trap };
    assert(Code(highAbort) == "GIR-V010");
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

void RejectsPassingAReadOnlyStructFieldToAMutatingCall() {
    auto m = ScalarStruct();
    auto u8 = m.IntType(CoreIntTy::U8);
    auto record = Main(m).slots[0].ty;
    auto readonlyRecord = m.RefType(CoreMut::Const, record);
    auto mutableU8 = m.RefType(CoreMut::Mut, u8);

    GirFunc mutate;
    mutate.name = "mutate";
    mutate.params = { mutableU8 };
    mutate.scopes = { -1 };
    mutate.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    mutate.summary.writes = { CoreTarget { false, 0 } };
    GirBlock mutateBody;
    mutateBody.params = { { 0, mutableU8 } };
    auto replacement = Int(m, 1, "9");
    replacement.ty = u8;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 0;
    store.b = 1;
    store.org = 0;
    mutateBody.insts = { replacement, store, Ret() };
    mutate.blocks = { mutateBody };

    GirFunc readonly;
    readonly.name = "readonly";
    readonly.params = { readonlyRecord };
    readonly.scopes = { -1 };
    readonly.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    readonly.summary.writes = { CoreTarget { false, 0 } };
    GirBlock readonlyEntry, readonlyTarget;
    readonlyEntry.params = { { 0, readonlyRecord } };
    auto field = Def(GirOp::Field, 1);
    field.a = 0;
    field.idx = 0;
    readonlyEntry.insts = { field, Br(1, { 1 }) };
    readonlyTarget.params = { { 2, mutableU8 } };
    auto call = Def(GirOp::Call, 3);
    call.idx = 1;
    call.vals = { 2 };
    call.org = 0;
    readonlyTarget.insts = { call, Ret() };
    readonly.blocks = { readonlyEntry, readonlyTarget };

    m.funcs.push_back(mutate);
    m.funcs.push_back(readonly);
    assert(Code(m) == "GIR-V030");
}

void OwnerArrayElementsRemainWritable() {
    auto m = Base();
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType array;
    array.kind = CoreType::Arr;
    array.elem = i64;
    array.count = 1;
    auto arrayType = m.Intern(array);
    Main(m).slots = { { arrayType, CoreVarKind::Let, 0, 0 } };

    auto initial = Int(m, 0, "1");
    auto values = Def(GirOp::Arr, 1);
    values.ty = arrayType;
    values.vals = { 0 };
    auto init = Init(0, 1);
    auto owner = Def(GirOp::Slot, 2);
    owner.idx = 0;
    auto snapshot = Def(GirOp::Snap, 3);
    snapshot.snap = GirSnapshotMode::Owner;
    snapshot.a = 2;
    auto index = Int(m, 4, "0");
    auto element = Def(GirOp::Index, 5);
    element.a = 3;
    element.b = 4;
    element.org = 0;
    auto replacement = Int(m, 6, "2");
    GirInst store;
    store.op = GirOp::Store;
    store.a = 5;
    store.b = 6;
    store.org = 0;
    Main(m).summary.aborts = true;
    Main(m).blocks[0].insts = {
        Enter(0), initial, values, init, owner, snapshot, index, element, replacement, store,
        Leave(0), Ret(),
    };
    assert(Code(m) == "");
}

void OwnerGrowElementsRemainWritable() {
    auto m = Base();
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType grow;
    grow.kind = CoreType::Grow;
    grow.elem = i64;
    auto growType = m.Intern(grow);
    Main(m).slots = { { growType, CoreVarKind::Let, 0, 0 } };

    auto initial = Int(m, 0, "1");
    auto values = Def(GirOp::Arr, 1);
    values.ty = growType;
    values.vals = { 0 };
    auto init = Init(0, 1);
    auto owner = Def(GirOp::Slot, 2);
    owner.idx = 0;
    auto snapshot = Def(GirOp::Snap, 3);
    snapshot.snap = GirSnapshotMode::Owner;
    snapshot.a = 2;
    auto index = Int(m, 4, "0");
    index.ty = i64;
    auto element = Def(GirOp::Index, 5);
    element.a = 3;
    element.b = 4;
    element.org = 0;
    auto replacement = Int(m, 6, "2");
    GirInst store;
    store.op = GirOp::Store;
    store.a = 5;
    store.b = 6;
    store.org = 0;
    Main(m).summary.aborts = true;
    Main(m).blocks[0].insts = {
        Enter(0), initial, values, init, owner, snapshot, index, element, replacement, store,
        Leave(0), Ret(),
    };
    assert(Code(m) == "");
}

void MutableSliceCallResultsRemainWritable() {
    auto m = Base();
    auto u8 = m.IntType(CoreIntTy::U8);
    auto i64 = m.IntType(CoreIntTy::I64);
    auto slice = m.SliceType(CoreMut::Mut, u8);

    GirFunc identity;
    identity.name = "identity";
    identity.params = { slice };
    identity.results = { slice };
    identity.scopes = { -1 };
    identity.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    identity.roots.results = { { CoreRootRef { CoreRootRef::Param, 0 } } };
    GirBlock identityBody;
    identityBody.params = { { 0, slice } };
    identityBody.insts = { Ret({ 0 }) };
    identity.blocks = { identityBody };
    m.funcs.push_back(identity);

    GirFunc update;
    update.name = "update";
    update.params = { slice };
    update.slots = { { slice, CoreVarKind::Let, 0, 0 } };
    update.scopes = { -1 };
    update.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    update.summary.writes = { CoreTarget { false, 0 } };
    update.summary.aborts = true;
    GirBlock updateBody;
    updateBody.params = { { 0, slice } };
    auto call = Def(GirOp::Call, 1);
    call.idx = 1;
    call.vals = { 0 };
    call.org = 0;
    auto init = Init(0, 1);
    auto slot = Def(GirOp::Slot, 2);
    slot.idx = 0;
    auto loaded = Def(GirOp::Load, 3);
    loaded.a = 2;
    auto view = Def(GirOp::SliceView, 4);
    view.a = 3;
    auto index = Int(m, 5, "0");
    index.ty = i64;
    auto element = Def(GirOp::Index, 6);
    element.a = 4;
    element.b = 5;
    element.org = 0;
    auto replacement = Int(m, 7, "9");
    replacement.ty = u8;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 6;
    store.b = 7;
    store.org = 0;
    updateBody.insts = {
        Enter(0), call, init, slot, loaded, view, index, element, replacement, store,
        Leave(0), Ret(),
    };
    update.blocks = { updateBody };
    m.funcs.push_back(update);
    assert(Code(m) == "");
}

void MutableSliceParametersRemainWritable() {
    auto m = Base();
    auto u8 = m.IntType(CoreIntTy::U8);
    auto slice = m.SliceType(CoreMut::Mut, u8);
    GirFunc update;
    update.name = "update";
    update.params = { slice };
    update.scopes = { -1 };
    update.summary.unknown = true;
    update.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    GirBlock body;
    body.params = { { 0, slice } };
    auto snapshot = Def(GirOp::SliceView, 1);
    snapshot.a = 0;
    auto index = Int(m, 2, "0");
    index.ty = m.IntType(CoreIntTy::I64);
    auto element = Def(GirOp::Index, 3);
    element.a = 1;
    element.b = 2;
    element.org = 0;
    auto replacement = Int(m, 4, "9");
    replacement.ty = u8;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 3;
    store.b = 4;
    store.org = 0;
    body.insts = { snapshot, index, element, replacement, store, Ret() };
    update.blocks = { body };
    m.funcs.push_back(update);
    assert(Code(m) == "");
}

void RejectsReturningAFieldRefFromAReadOnlyOwner() {
    auto m = ScalarStruct();
    auto u8 = m.IntType(CoreIntTy::U8);
    auto record = Main(m).slots[0].ty;
    auto readonlyRecord = m.RefType(CoreMut::Const, record);
    auto mutableU8 = m.RefType(CoreMut::Mut, u8);
    GirFunc leak;
    leak.name = "leak";
    leak.params = { readonlyRecord };
    leak.results = { mutableU8 };
    leak.scopes = { -1 };
    leak.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    leak.roots.results = { { CoreRootRef { CoreRootRef::Param, 0 } } };
    leak.summary.unknown = true;
    GirBlock body;
    body.params = { { 0, readonlyRecord } };
    auto field = Def(GirOp::Field, 1);
    field.a = 0;
    field.idx = 0;
    body.insts = { field, Ret({ 1 }) };
    leak.blocks = { body };
    m.funcs.push_back(leak);
    assert(Code(m) == "GIR-V030");
}

void RejectsMaterializingAFieldRefFromAReadOnlyOwner() {
    auto m = ScalarStruct();
    auto u8 = m.IntType(CoreIntTy::U8);
    auto record = Main(m).slots[0].ty;
    auto readonlyRecord = m.RefType(CoreMut::Const, record);
    auto mutableU8 = m.RefType(CoreMut::Mut, u8);
    GirFunc save;
    save.name = "save";
    save.params = { readonlyRecord };
    save.slots = { { mutableU8, CoreVarKind::Let, 0, 0 } };
    save.scopes = { -1 };
    save.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    save.summary.unknown = true;
    GirBlock body;
    body.params = { { 0, readonlyRecord } };
    auto field = Def(GirOp::Field, 1);
    field.a = 0;
    field.idx = 0;
    auto init = Init(0, 1);
    body.insts = { field, init, Ret() };
    save.blocks = { body };
    m.funcs.push_back(save);
    assert(Code(m) == "GIR-V030");
}

void RejectsPassingAContentsConstAggregateFieldToAMutatingCall() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto u8 = m.IntType(CoreIntTy::U8);
    auto inner = StructType(m, 0);
    auto outer = StructType(m, 1);
    m.structs = {
        CoreStruct { 1, { CoreField { u8, CoreVarKind::Var, CoreMut::Mut, 0 } } },
        CoreStruct { 1, { CoreField { inner, CoreVarKind::Var, CoreMut::Const, 0 } } },
    };
    Main(m).slots = { { outer, CoreVarKind::Let, 0, 0 } };
    auto refInner = m.RefType(CoreMut::Mut, inner);
    GirFunc mutate;
    mutate.name = "mutate";
    mutate.params = { refInner };
    mutate.scopes = { -1 };
    mutate.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    mutate.summary.unknown = true;
    GirBlock mutateBody;
    mutateBody.params = { { 0, refInner } };
    auto leaf = Def(GirOp::Field, 1);
    leaf.a = 0;
    leaf.idx = 0;
    auto replacement = Int(m, 2, "9");
    replacement.ty = u8;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 1;
    store.b = 2;
    store.org = 0;
    mutateBody.insts = { leaf, replacement, store, Ret() };
    mutate.blocks = { mutateBody };
    m.funcs.push_back(mutate);

    auto initial = Int(m, 0, "1");
    initial.ty = u8;
    auto innerValue = Def(GirOp::Struct, 1);
    innerValue.ty = inner;
    innerValue.vals = { 0 };
    auto outerValue = Def(GirOp::Struct, 2);
    outerValue.ty = outer;
    outerValue.vals = { 1 };
    auto init = Init(0, 2);
    auto owner = Def(GirOp::Slot, 3);
    owner.idx = 0;
    auto field = Def(GirOp::Field, 4);
    field.a = 3;
    field.idx = 0;
    auto call = Def(GirOp::Call, 5);
    call.idx = 1;
    call.vals = { 4 };
    call.org = 0;
    Main(m).summary.unknown = true;
    Main(m).blocks[0].insts = { Enter(0), initial, innerValue, outerValue, init, owner, field, call, Leave(0), Ret() };
    assert(Code(m) == "GIR-V030");
}

void AcceptsNestedFieldContentsThroughAJoin() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto u8 = m.IntType(CoreIntTy::U8);
    auto inner = StructType(m, 0);
    auto outer = StructType(m, 1);
    m.structs = {
        CoreStruct { 1, { CoreField { u8, CoreVarKind::Var, CoreMut::Mut, 0 } } },
        CoreStruct { 1, { CoreField { inner, CoreVarKind::Let, CoreMut::Mut, 0 } } },
    };
    Main(m).slots = { { outer, CoreVarKind::Let, 0, 0 } };

    auto initValue = Int(m, 0, "1");
    initValue.ty = u8;
    auto innerValue = Def(GirOp::Struct, 1);
    innerValue.ty = inner;
    innerValue.vals = { 0 };
    auto outerValue = Def(GirOp::Struct, 2);
    outerValue.ty = outer;
    outerValue.vals = { 1 };
    auto init = Init(0, 2);
    auto owner = Def(GirOp::Slot, 3);
    owner.idx = 0;
    auto nested = Def(GirOp::Field, 4);
    nested.a = 3;
    nested.idx = 0;
    GirBlock entry;
    entry.insts = { Enter(0), initValue, innerValue, outerValue, init, owner, nested, Br(1, { 4 }) };

    auto readonlyInner = m.RefType(CoreMut::Const, inner);
    GirBlock join;
    join.params = { { 5, readonlyInner } };
    auto leaf = Def(GirOp::Field, 6);
    leaf.a = 5;
    leaf.idx = 0;
    auto replacement = Int(m, 7, "9");
    replacement.ty = u8;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 6;
    store.b = 7;
    store.org = 0;
    join.insts = { leaf, replacement, store, Leave(0), Ret() };
    Main(m).blocks = { entry, join };
    assert(Code(m) == "");
}

void RejectsArrayElementWriteThroughConstFieldContents() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto u8 = m.IntType(CoreIntTy::U8);
    CoreType array;
    array.kind = CoreType::Arr;
    array.elem = u8;
    array.count = 2;
    auto arrayType = m.Intern(array);
    auto record = StructType(m, 0);
    m.structs = { CoreStruct { 2, { CoreField { arrayType, CoreVarKind::Var, CoreMut::Const, 0 } } } };
    Main(m).slots = { { record, CoreVarKind::Let, 0, 0 } };

    auto first = Int(m, 0, "1");
    first.ty = u8;
    auto second = Int(m, 1, "2");
    second.ty = u8;
    auto elements = Def(GirOp::Arr, 2);
    elements.ty = arrayType;
    elements.vals = { 0, 1 };
    auto value = Def(GirOp::Struct, 3);
    value.ty = record;
    value.vals = { 2 };
    auto init = Init(0, 3);
    auto owner = Def(GirOp::Slot, 4);
    owner.idx = 0;
    auto field = Def(GirOp::Field, 5);
    field.a = 4;
    field.idx = 0;
    auto view = Def(GirOp::Snap, 6);
    view.snap = GirSnapshotMode::Owner;
    view.a = 5;
    auto index = Int(m, 7, "0");
    index.ty = m.IntType(CoreIntTy::I64);
    auto element = Def(GirOp::Index, 8);
    element.a = 6;
    element.b = 7;
    auto replacement = Int(m, 9, "9");
    replacement.ty = u8;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 8;
    store.b = 9;
    store.org = 0;
    Main(m).blocks[0].insts = {
        Enter(0), first, second, elements, value, init, owner, field, view, index, element,
        replacement, store, Leave(0), Ret(),
    };
    assert(Code(m) == "GIR-V030");
}

void FieldProjectionKeepsItsOwnerRoot() {
    auto m = ScalarStruct();
    auto u8 = m.IntType(CoreIntTy::U8);
    auto record = Main(m).slots[0].ty;

    GirFunc leak;
    leak.name = "leak";
    leak.results = { m.RefType(CoreMut::Mut, u8) };
    leak.slots = { { record, CoreVarKind::Let, 0, 0 } };
    leak.scopes = { -1 };
    leak.roots.results = { {} };
    leak.summary.unknown = true;
    auto first = Int(m, 0, "5");
    first.ty = u8;
    auto second = Int(m, 1, "7");
    auto make = Def(GirOp::Struct, 2);
    make.ty = record;
    make.vals = { 0, 1 };
    auto init = Init(0, 2);
    auto owner = Def(GirOp::Slot, 3);
    owner.idx = 0;
    auto field = Def(GirOp::Field, 4);
    field.a = 3;
    field.idx = 0;
    GirBlock body;
    body.insts = { Enter(0), first, second, make, init, owner, field, Leave(0), Ret({ 4 }) };
    leak.blocks = { body };
    m.funcs.push_back(leak);
    assert(Code(m) == "GIR-V050");
}

void FieldProjectionKeepsGlobalReadAndWriteEffects() {
    auto m = ScalarStruct();
    auto record = Main(m).slots[0].ty;
    auto u8 = m.IntType(CoreIntTy::U8);
    GirGlobal global;
    global.name = "record";
    global.ty = record;
    global.kind = CoreVarKind::Var;
    global.org = 0;
    global.init.name = "record";
    global.init.results = { record };
    global.init.summary.unknown = true;
    auto first = Int(m, 0, "5");
    first.ty = u8;
    auto second = Int(m, 1, "7");
    auto make = Def(GirOp::Struct, 2);
    make.ty = record;
    make.vals = { 0, 1 };
    global.init.blocks = { GirBlock { {}, { first, second, make, Ret({ 2 }) } } };
    m.globals.push_back(global);

    auto address = Def(GirOp::Global, 0);
    address.idx = 0;
    auto field = Def(GirOp::Field, 1);
    field.a = 0;
    field.idx = 0;
    auto value = Int(m, 2, "9");
    value.ty = u8;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 1;
    store.b = 2;
    store.org = 0;
    auto load = Def(GirOp::Load, 3);
    load.a = 1;
    Main(m).blocks[0].insts = { address, field, value, store, load, Ret() };
    Main(m).summary.outputs = true;
    assert(Code(m) == "GIR-V050");
    Main(m).summary.writes = { CoreTarget { true, 0 } };
    assert(Code(m) == "GIR-V050");
    Main(m).summary.reads = { CoreTarget { true, 0 } };
    assert(Code(m) == "");
}

void FieldCallArgumentsKeepTheirOwnerRoot() {
    auto m = ScalarStruct();
    auto record = Main(m).slots[0].ty;
    auto u8 = m.IntType(CoreIntTy::U8);
    auto refU8 = m.RefType(CoreMut::Mut, u8);
    GirFunc callee;
    callee.name = "read";
    callee.params = { refU8 };
    callee.scopes = { -1 };
    callee.blocks = { GirBlock { { { 0, refU8 } }, { Ret() } } };
    m.funcs.push_back(callee);

    auto one = Int(m, 0, "5");
    one.ty = u8;
    auto two = Int(m, 1, "7");
    auto make = Def(GirOp::Struct, 2);
    make.ty = record;
    make.vals = { 0, 1 };
    auto init = Init(0, 2);
    auto owner = Def(GirOp::Slot, 3);
    owner.idx = 0;
    auto field = Def(GirOp::Field, 4);
    field.a = 3;
    field.idx = 0;
    auto call = Def(GirOp::Call, 5);
    call.idx = 1;
    call.vals = { 4 };
    call.org = 0;
    Main(m).blocks[0].insts = { Enter(0), one, two, make, init, owner, field, call, Leave(0), Ret() };
    assert(Code(m) == "GIR-V050");
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

void LoweredFieldArrayViewsKeepOwnerContents() {
    // A `let` field cannot be replaced, but its `mut` contents remain writable.
    assert(CoreLoweringCode(LetArrayFieldCase(false)) == "");
    assert(CoreLoweringCode(LetArrayFieldCase(true)) == "");
    assert(CoreLoweringCode(LetArrayFieldCase(false, CoreMut::Const)) == "GIR-V030");
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
    assert((copySizes == vector<string>{ "1", "8", "9", "1", "8", "8" }));
}

void NestedStructAndFixedArrayFieldsUseByteStorage() {
    auto high = Base();
    high.profile = CoreProfile::Shrink;
    auto u8 = high.IntType(CoreIntTy::U8);
    auto i64 = high.IntType(CoreIntTy::I64);
    auto inner = StructType(high, 0);
    CoreType cellArray;
    cellArray.kind = CoreType::Arr;
    cellArray.elem = i64;
    cellArray.count = 2;
    auto cells = high.Intern(cellArray);
    CoreType nestedArray;
    nestedArray.kind = CoreType::Arr;
    nestedArray.elem = inner;
    nestedArray.count = 2;
    auto nested = high.Intern(nestedArray);
    auto outer = StructType(high, 1);
    high.structs = {
        CoreStruct { 9, {
            CoreField { u8, CoreVarKind::Var, CoreMut::Mut, 0 },
            CoreField { i64, CoreVarKind::Var, CoreMut::Mut, 1 },
        } },
        CoreStruct { 43, {
            CoreField { inner, CoreVarKind::Var, CoreMut::Mut, 0 },
            CoreField { cells, CoreVarKind::Var, CoreMut::Mut, 9 },
            CoreField { nested, CoreVarKind::Var, CoreMut::Mut, 25 },
        } },
    };
    Main(high).slots = {
        { outer, CoreVarKind::Let, 0, 0 },
        { outer, CoreVarKind::Let, 0, 1 },
    };
    Main(high).summary.aborts = true;
    Main(high).summary.outputs = true;

    auto firstTag = Int(high, 0, "1");
    firstTag.ty = u8;
    auto firstValue = Int(high, 1, "2");
    auto firstInner = Def(GirOp::Struct, 2);
    firstInner.ty = inner;
    firstInner.vals = { 0, 1 };
    auto secondTag = Int(high, 3, "3");
    secondTag.ty = u8;
    auto secondValue = Int(high, 4, "4");
    auto secondInner = Def(GirOp::Struct, 5);
    secondInner.ty = inner;
    secondInner.vals = { 3, 4 };
    auto cellValues = Def(GirOp::Arr, 6);
    cellValues.ty = cells;
    cellValues.vals = { 1, 4 };
    auto nestedValues = Def(GirOp::Arr, 7);
    nestedValues.ty = nested;
    nestedValues.vals = { 2, 5 };
    auto outerValue = Def(GirOp::Struct, 8);
    outerValue.ty = outer;
    outerValue.vals = { 2, 6, 7 };
    auto init = Init(0, 8);
    auto copy = Init(1, 8);

    auto owner = Def(GirOp::Slot, 9);
    owner.idx = 0;
    auto innerField = Def(GirOp::Field, 10);
    innerField.a = 9;
    innerField.idx = 0;
    auto innerValue = Def(GirOp::Field, 11);
    innerValue.a = 10;
    innerValue.idx = 1;
    auto newInnerValue = Int(high, 12, "10");
    GirInst storeInner;
    storeInner.op = GirOp::Store;
    storeInner.a = 11;
    storeInner.b = 12;
    storeInner.org = 0;

    auto cellsField = Def(GirOp::Field, 13);
    cellsField.a = 9;
    cellsField.idx = 1;
    auto cellsView = Def(GirOp::Snap, 14);
    cellsView.snap = GirSnapshotMode::Owner;
    cellsView.a = 13;
    auto cellIndex = Int(high, 15, "1");
    auto cell = Def(GirOp::Index, 16);
    cell.a = 14;
    cell.b = 15;
    cell.org = 0;
    auto newCell = Int(high, 17, "11");
    GirInst storeCell;
    storeCell.op = GirOp::Store;
    storeCell.a = 16;
    storeCell.b = 17;
    storeCell.org = 0;

    auto nestedField = Def(GirOp::Field, 18);
    nestedField.a = 9;
    nestedField.idx = 2;
    auto nestedView = Def(GirOp::Snap, 19);
    nestedView.snap = GirSnapshotMode::Owner;
    nestedView.a = 18;
    auto nestedIndex = Int(high, 20, "1");
    auto nestedElement = Def(GirOp::Index, 21);
    nestedElement.a = 19;
    nestedElement.b = 20;
    nestedElement.org = 0;
    auto nestedValue = Def(GirOp::Field, 22);
    nestedValue.a = 21;
    nestedValue.idx = 1;
    auto newNestedValue = Int(high, 23, "12");
    GirInst storeNested;
    storeNested.op = GirOp::Store;
    storeNested.a = 22;
    storeNested.b = 23;
    storeNested.org = 0;

    auto copyOwner = Def(GirOp::Slot, 24);
    copyOwner.idx = 1;
    auto copyInner = Def(GirOp::Field, 25);
    copyInner.a = 24;
    copyInner.idx = 0;
    auto copyValuePlace = Def(GirOp::Field, 26);
    copyValuePlace.a = 25;
    copyValuePlace.idx = 1;
    auto copyValue = Def(GirOp::Load, 27);
    copyValue.a = 26;
    GirInst printCopy;
    printCopy.op = GirOp::Print;
    printCopy.parts = { { false, "", 27 } };
    printCopy.org = 0;
    Main(high).blocks[0].insts = {
        Enter(0), firstTag, firstValue, firstInner, secondTag, secondValue, secondInner,
        cellValues, nestedValues, outerValue, init, copy, owner, innerField, innerValue,
        newInnerValue, storeInner, cellsField, cellsView, cellIndex, cell, newCell, storeCell,
        nestedField, nestedView, nestedIndex, nestedElement, nestedValue, newNestedValue,
        storeNested, copyOwner, copyInner, copyValuePlace, copyValue, printCopy, Leave(0), Ret(),
    };

    assert(Code(high) == "");
    auto low = GirToLow(high).Lower();
    assert(!GirVerifier(low).Verify());
    assert(low.structs.empty());
    auto copies = 0;
    auto offsets = 0;
    for (auto &block : low.funcs[0].blocks)
        for (auto &inst : block.insts) {
            copies += inst.op == GirOp::BytesCopy;
            offsets += inst.op == GirOp::PtrOffset;
        }
    assert(copies >= 8);
    assert(offsets >= 6);
}

void LowAggregateLoopParametersOwnSnapshots() {
    // The constructor runs before reading the old block value. If its frame
    // temporary aliases that value, the loop prints 0, 2 instead of 0, 1.
    auto exercise = [](bool fixedArray) {
        auto m = Base();
        m.profile = CoreProfile::Shrink;
        auto i64 = m.IntType(CoreIntTy::I64);
        GirTypeId aggregate;
        if (fixedArray) {
            CoreType array;
            array.kind = CoreType::Arr;
            array.elem = i64;
            array.count = 1;
            aggregate = m.Intern(array);
        } else {
            aggregate = StructType(m, 0);
            m.structs = { CoreStruct { 8, { CoreField { i64, CoreVarKind::Var, CoreMut::Mut, 0 } } } };
        }
        Main(m).scopes = { -1, 0 };
        Main(m).slots = { { aggregate, CoreVarKind::Let, 1, 0 } };
        Main(m).summary.aborts = true;
        Main(m).summary.outputs = true;

        GirBlock entry, loop, done;
        auto initialField = Int(m, 0, "0");
        auto initial = Def(fixedArray ? GirOp::Arr : GirOp::Struct, 1);
        initial.ty = aggregate;
        initial.vals = { 0 };
        auto firstCount = Int(m, 2, "1");
        entry.insts = { Enter(0), initialField, initial, firstCount, Br(1, { 1, 2 }) };

        loop.params = { { 3, aggregate }, { 4, i64 } };
        auto next = Def(fixedArray ? GirOp::Arr : GirOp::Struct, 5);
        next.ty = aggregate;
        next.vals = { 4 };
        auto saveOld = Init(0, 3);
        auto slot = Def(GirOp::Slot, 6);
        slot.idx = 0;
        auto nextValue = 7;
        int oldField = -1;
        vector<GirInst> readOld { slot };
        if (fixedArray) {
            auto snapshot = Def(GirOp::Snap, nextValue++);
            snapshot.snap = GirSnapshotMode::Owner;
            snapshot.a = 6;
            auto index = Int(m, nextValue++, "0");
            auto element = Def(GirOp::Index, nextValue++);
            element.a = snapshot.res;
            element.b = index.res;
            element.org = 0;
            auto load = Def(GirOp::Load, nextValue++);
            load.a = element.res;
            readOld.insert(readOld.end(), { snapshot, index, element, load });
            oldField = load.res;
        } else {
            auto field = Def(GirOp::Field, nextValue++);
            field.a = 6;
            field.idx = 0;
            auto load = Def(GirOp::Load, nextValue++);
            load.a = field.res;
            readOld.insert(readOld.end(), { field, load });
            oldField = load.res;
        }
        GirInst print;
        print.op = GirOp::Print;
        print.parts = { { false, "", oldField } };
        print.org = 0;
        auto continueCount = Int(m, nextValue++, "1");
        auto compare = Def(GirOp::Cmp, nextValue++);
        compare.ty = i64;
        compare.cmp = CoreCmpOp::Eq;
        compare.a = 4;
        compare.b = continueCount.res;
        auto followingCount = Def(GirOp::Next, nextValue++);
        followingCount.ty = i64;
        followingCount.a = 4;
        auto branch = CondBr(compare.res, 1, 2);
        branch.vals = { next.res, followingCount.res };
        loop.insts = { Enter(1), next, saveOld };
        loop.insts.insert(loop.insts.end(), readOld.begin(), readOld.end());
        loop.insts.insert(loop.insts.end(), { print, Leave(1), continueCount, compare, followingCount, branch });
        done.insts = { Leave(0), Ret() };
        Main(m).blocks = { entry, loop, done };

        assert(Code(m) == "");
        auto low = GirToLow(m).Lower();
        assert(!GirVerifier(low).Verify());
        auto &lowLoop = low.funcs[0].blocks[1];
        assert(lowLoop.params.size() == 1);
        assert(low.Type(lowLoop.params[0].second).kind == CoreType::Int);
        bool loopEdgeCopiesAggregate = false;
        for (auto &source : low.funcs[0].blocks) {
            if (source.insts.empty() || source.insts.back().op != GirOp::CondBr) continue;
            auto &branch = source.insts.back();
            for (auto edge : { branch.idx, branch.idx2 }) {
                auto &edgeBlock = low.funcs[0].blocks[edge];
                auto &edgeTerm = edgeBlock.insts.back();
                if (edgeTerm.op != GirOp::Br || edgeTerm.idx != 1) continue;
                loopEdgeCopiesAggregate = any_of(edgeBlock.insts.begin(), edgeBlock.insts.end(),
                                                 [](auto &i) { return i.op == GirOp::BytesCopy; });
            }
        }
        assert(loopEdgeCopiesAggregate);
    };
    exercise(false);
    exercise(true);
}

void LowKeepsPackedFieldAlignmentAcrossBlockParameters() {
    auto high = ScalarStruct();
    auto &f = Main(high);
    auto u8 = high.IntType(CoreIntTy::U8);
    auto refU8 = high.RefType(CoreMut::Mut, u8);

    auto one = Int(high, 0, "5");
    one.ty = u8;
    auto two = Int(high, 1, "7");
    auto make = Def(GirOp::Struct, 2);
    make.ty = f.slots[0].ty;
    make.vals = { 0, 1 };
    auto init = Init(0, 2);
    auto owner = Def(GirOp::Slot, 3);
    owner.idx = 0;
    auto field = Def(GirOp::Field, 4);
    field.a = 3;
    field.idx = 0;
    GirBlock entry;
    entry.insts = { Enter(0), one, two, make, init, owner, field, Br(1, { 4 }) };

    GirBlock join;
    join.params = { { 5, refU8 } };
    auto replacement = Int(high, 6, "9");
    replacement.ty = u8;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 5;
    store.b = 6;
    store.org = 0;
    auto load = Def(GirOp::Load, 7);
    load.a = 5;
    GirInst print;
    print.op = GirOp::Print;
    print.parts = { { false, "", 7 } };
    print.org = 0;
    join.insts = { replacement, store, load, print, Leave(0), Ret() };
    f.blocks = { entry, join };

    assert(Code(high) == "");
    auto low = GirToLow(high).Lower();
    assert(!GirVerifier(low).Verify());
    auto scalarLoads = 0;
    auto scalarStores = 0;
    for (auto &block : low.funcs[0].blocks)
        for (auto &inst : block.insts) {
            scalarLoads += inst.op == GirOp::PLoad;
            scalarStores += inst.op == GirOp::PStore;
        }
    assert(scalarLoads == 0);
    assert(scalarStores == 0);
}

void LowKeepsPackedFieldAlignmentAcrossCallParametersAndResults() {
    auto high = ScalarStruct();
    auto &f = Main(high);
    auto u8 = high.IntType(CoreIntTy::U8);
    auto refU8 = high.RefType(CoreMut::Mut, u8);

    GirFunc relay;
    relay.name = "relay";
    relay.params = { refU8 };
    relay.results = { refU8 };
    relay.scopes = { -1 };
    relay.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    relay.roots.results = { { CoreRootRef { CoreRootRef::Param, 0 } } };
    relay.summary.unknown = true;
    relay.blocks = { GirBlock { { { 0, refU8 } }, { Ret({ 0 }) } } };

    auto one = Int(high, 0, "5");
    one.ty = u8;
    auto two = Int(high, 1, "7");
    auto make = Def(GirOp::Struct, 2);
    make.ty = f.slots[0].ty;
    make.vals = { 0, 1 };
    auto init = Init(0, 2);
    auto owner = Def(GirOp::Slot, 3);
    owner.idx = 0;
    auto field = Def(GirOp::Field, 4);
    field.a = 3;
    field.idx = 0;
    auto call = Def(GirOp::Call, 5);
    call.idx = 1;
    call.vals = { 4 };
    call.org = 0;
    auto replacement = Int(high, 6, "9");
    replacement.ty = u8;
    GirInst store;
    store.op = GirOp::Store;
    store.a = 5;
    store.b = 6;
    store.org = 0;
    auto load = Def(GirOp::Load, 7);
    load.a = 5;
    GirInst print;
    print.op = GirOp::Print;
    print.parts = { { false, "", 7 } };
    print.org = 0;
    f.summary.outputs = true;
    f.summary.unknown = true;
    f.blocks[0].insts = {
        Enter(0), one, two, make, init, owner, field, call, replacement, store, load, print,
        Leave(0), Ret(),
    };
    high.funcs.push_back(relay);

    assert(Code(high) == "");
    auto low = GirToLow(high).Lower();
    assert(!GirVerifier(low).Verify());
    auto scalarLoads = 0;
    auto scalarStores = 0;
    for (auto &func : low.funcs) for (auto &block : func.blocks) for (auto &inst : block.insts) {
        scalarLoads += inst.op == GirOp::PLoad;
        scalarStores += inst.op == GirOp::PStore;
    }
    assert(scalarLoads == 0);
    assert(scalarStores == 0);
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
    RejectsDuplicateVariablesForReferenceToSliceParameterSlots();
    RejectsSlotVariableThatNamesAnotherReferenceToSliceParameter();
    RejectsSummaryThatOmitsAGlobalReachedThroughACalleeParameter();
    RejectsParameterRootUnderapproximationAtCall();
    AcceptsUnreachableAfterANonReturningCall();
    RejectsUnreachableWithoutANonReturningCall();
    RejectsAbortingOperationWithoutOrigin();
    LowAccepts();
    RejectsHighOperationInLowModule();
    RejectsTwoResizablesOnOneStack();
    RejectsWatermarkPastCallerOwnedRegion();
    PassedOwnerPairsKeepTheirExactIdentity();
    RejectsReplacementThroughALetOwnerPhi();
    RejectsUnresolvedLayout();
    RejectsElementsThatDoNotTopTheirStack();
    PilotAndShrinkModuleShapesStayDistinct();
    CoreShrinkPushAndSummaryCarryOriginsAndShrinks();
    CoreShrinkOperationTagsAndPlaceTypingAreCanonical();
    CoreShrinkOperationsLowerToVerifiedGir();
    ResizeChecksFollowNegativeSizeAndEvaluateFillFirst();
    LimitedAppendChecksCapacityBeforeWriting();
    AggregatePopCopiesBeforeReleasingItsStack();
    LimitedClearStoresItsLengthInByteStorage();
    PilotLetGrowPushUsesContentsPermission();
    LetLimitedOwnerSupportsDirectPushPopAndClear();
    RejectsPassingALetLimitedOwnerAsAMutableReference();
    ShrinkSummariesSerializeAndCoverPopEffects();
    AppendSummaryIncludesItsViewSourceRead();
    ShrinkOperationsAndAbortTagsStayOutOfPilotGir();
    AcceptsScalarStructFieldsOnAnImmutableBinding();
    RejectsStructsInThePilotProfile();
    RejectsAStoreToALetField();
    RejectsAWriteThroughConstFieldContents();
    LowKeepsPackedFieldAlignmentAcrossBlockParameters();
    RejectsAConstructorWithAnotherNominalType();
    RejectsAFieldComponentAfterItsStructType();
    RejectsAnInvalidStructLayout();
    LoweredFieldArrayViewsKeepOwnerContents();
    LowStructUsesByteStorageAndUnalignedSafeAccess();
    NestedStructAndFixedArrayFieldsUseByteStorage();
    LowAggregateLoopParametersOwnSnapshots();
    AcceptsNestedFieldContentsThroughAJoin();
    RejectsArrayElementWriteThroughConstFieldContents();
    FieldProjectionKeepsItsOwnerRoot();
    FieldProjectionKeepsGlobalReadAndWriteEffects();
    FieldCallArgumentsKeepTheirOwnerRoot();
    RejectsPassingAReadOnlyStructFieldToAMutatingCall();
    OwnerArrayElementsRemainWritable();
    OwnerGrowElementsRemainWritable();
    MutableSliceCallResultsRemainWritable();
    MutableSliceParametersRemainWritable();
    RejectsReturningAFieldRefFromAReadOnlyOwner();
    RejectsMaterializingAFieldRefFromAReadOnlyOwner();
    RejectsPassingAContentsConstAggregateFieldToAMutatingCall();
    LowKeepsPackedFieldAlignmentAcrossCallParametersAndResults();
    puts("compiler_gir ok");
    return 0;
}
