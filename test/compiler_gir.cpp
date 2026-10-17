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
#include "../src/gir/gir_evidence.h"
#include "../src/gir/gir_low.h"
#include "../src/gir/gir_json.h"
#include "../src/gir/gir_verify.h"

using namespace goose;

namespace {

GirInst Def(GirOp op, int res) {
    GirInst i;
    i.op = op;
    i.res = res;
    if (op == GirOp::DestFinish) i.org = 0;
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
GirInst Ret(vector<int> vals = {}) { GirInst i; i.op = GirOp::Ret; i.vals = std::move(vals); if (!i.vals.empty()) i.org = 0; return i; }
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

GirModule FixedIndexEvidenceModule() {
    auto m = Base();
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType array;
    array.kind = CoreType::Arr;
    array.elem = i64;
    array.count = 4;
    auto arrayTy = m.Intern(array);
    Main(m).slots = { { arrayTy, CoreVarKind::Var, 0, 0 } };
    Main(m).summary.unknown = true;

    vector<GirInst> instructions = { Enter(0) };
    for (int value = 0; value < 4; value++)
        instructions.push_back(Int(m, value, to_string(value).c_str()));
    auto literal = Def(GirOp::Arr, 4);
    literal.ty = arrayTy;
    literal.vals = { 0, 1, 2, 3 };
    instructions.push_back(literal);
    instructions.push_back(Init(0, 4));
    auto owner = Def(GirOp::Slot, 5);
    owner.idx = 0;
    instructions.push_back(owner);
    instructions.push_back(Int(m, 7, "2"));
    auto length = Def(GirOp::ArrayLen, 8);
    length.a = 5;
    instructions.push_back(length);
    auto view = Def(GirOp::Snap, 6);
    view.snap = GirSnapshotMode::Owner;
    view.a = 5;
    instructions.push_back(view);
    auto within = Def(GirOp::Cmp, 9);
    within.cmp = CoreCmpOp::Lt;
    within.ty = i64;
    within.a = 7;
    within.b = 8;
    instructions.push_back(within);
    instructions.push_back(CondBr(9, 1, 2));

    auto index = Def(GirOp::Index, 10);
    index.a = 6;
    index.b = 7;
    index.org = 0;
    auto load = Def(GirOp::Load, 11);
    load.a = 10;
    GirBlock success;
    success.insts = { index, load, Leave(0), Ret() };
    GirBlock failure;
    failure.insts = { Leave(0), Ret() };
    Main(m).blocks = { { {}, std::move(instructions) }, std::move(success), std::move(failure) };
    return m;
}

GirModule DynamicIndexEvidenceModule() {
    auto m = Base();
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType ownerType;
    ownerType.kind = CoreType::Grow;
    ownerType.elem = i64;
    auto grow = m.Intern(ownerType);
    Main(m).slots = { { grow, CoreVarKind::Var, 0, 0 } };
    Main(m).summary.unknown = true;

    auto literal = Def(GirOp::Arr, 1);
    literal.ty = grow;
    literal.vals = { 0 };
    auto owner = Def(GirOp::Slot, 2);
    owner.idx = 0;
    auto length = Def(GirOp::ArrayLen, 4);
    length.a = 2;
    auto within = Def(GirOp::Cmp, 5);
    within.cmp = CoreCmpOp::Lt;
    within.ty = i64;
    within.a = 3;
    within.b = 4;
    GirBlock entry;
    entry.insts = { Enter(0), Int(m, 0, "10"), literal, Init(0, 1), owner,
        Int(m, 3, "0"), length, within, CondBr(5, 1, 2) };

    auto view = Def(GirOp::Snap, 6);
    view.snap = GirSnapshotMode::Owner;
    view.a = 2;
    auto index = Def(GirOp::Index, 7);
    index.a = 6;
    index.b = 3;
    index.org = 0;
    auto load = Def(GirOp::Load, 8);
    load.a = 7;
    GirBlock success;
    success.insts = { view, index, load, Leave(0), Ret() };
    GirBlock failure;
    failure.insts = { Leave(0), Ret() };
    Main(m).blocks = { std::move(entry), std::move(success), std::move(failure) };
    return m;
}

void EvidenceProvesFixedIndexAndRejectsForgedProofs() {
    auto m = FixedIndexEvidenceModule();
    assert(Code(m) == "");
    ProposeGirEvidence(m);
    assert(Main(m).certificate.has_value());
    assert(Main(m).blocks[1].insts[0].op == GirOp::IndexProven);
    assert(Code(m) == "");

    auto missing = m;
    Main(missing).certificate.reset();
    assert(Code(missing) == "GIR-V080");

    auto falseFact = m;
    Main(falseFact).blocks[0].insts[8].text = "-1";
    assert(Code(falseFact) == "GIR-V080");

    auto forged = m;
    GirFact impossible;
    impossible.kind = GirFact::Lt;
    impossible.a = 8;
    impossible.b = 7;
    Main(forged).certificate->blocks[1].push_back(impossible);
    CanonicalGirFacts(Main(forged).certificate->blocks[1]);
    assert(Code(forged) == "GIR-V080");

    auto dynamic = DynamicIndexEvidenceModule();
    ProposeGirEvidence(dynamic);
    assert(Main(dynamic).blocks[1].insts[1].op == GirOp::IndexProven);
    assert(Code(dynamic) == "");

    auto afterCall = dynamic;
    GirFunc helper;
    helper.name = "helper";
    helper.blocks = { { {}, { Ret() } } };
    helper.summary.unknown = true;
    afterCall.funcs.push_back(std::move(helper));
    auto call = Def(GirOp::Call, 9);
    call.idx = 1;
    call.org = 0;
    Main(afterCall).blocks[1].insts.insert(Main(afterCall).blocks[1].insts.begin(), call);
    assert(Code(afterCall) == "GIR-V080");
}

void EvidenceDoesNotMergeDifferentBlockParameters() {
    auto m = Base();
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType array;
    array.kind = CoreType::Arr;
    array.elem = i64;
    array.count = 1;
    auto arrayType = m.Intern(array);
    auto referenceType = m.RefType(CoreMut::Mut, arrayType);
    Main(m).slots = { { arrayType, CoreVarKind::Var, 0, 0 } };
    Main(m).summary.unknown = true;

    auto condition = Def(GirOp::Bool, 1);
    condition.flag = true;
    auto literal = Def(GirOp::Arr, 2);
    literal.ty = arrayType;
    literal.vals = { 0 };
    GirBlock entry;
    entry.insts = { Enter(0), Int(m, 0, "0"), condition, literal, Init(0, 2), CondBr(1, 1, 2) };
    auto firstAddress = Def(GirOp::Slot, 3);
    firstAddress.idx = 0;
    GirBlock first;
    first.insts = { firstAddress, Br(3, { 3, 3 }) };
    auto secondAddress = Def(GirOp::Slot, 4);
    secondAddress.idx = 0;
    GirBlock second;
    second.insts = { secondAddress, Br(3, { 4, 4 }) };
    auto length = Def(GirOp::ArrayLen, 7);
    length.a = 5;
    auto view = Def(GirOp::Snap, 8);
    view.snap = GirSnapshotMode::Owner;
    view.a = 6;
    auto within = Def(GirOp::Cmp, 9);
    within.cmp = CoreCmpOp::Lt;
    within.ty = i64;
    within.a = 0;
    within.b = 7;
    GirBlock joined;
    joined.params = { { 5, referenceType }, { 6, referenceType } };
    joined.insts = { length, view, within, CondBr(9, 4, 5) };
    auto index = Def(GirOp::Index, 10);
    index.a = 8;
    index.b = 0;
    index.org = 0;
    auto load = Def(GirOp::Load, 11);
    load.a = 10;
    GirBlock success;
    success.insts = { index, load, Leave(0), Ret() };
    GirBlock failure;
    failure.insts = { Leave(0), Ret() };
    Main(m).blocks = { std::move(entry), std::move(first), std::move(second), std::move(joined),
                       std::move(success), std::move(failure) };
    assert(Code(m) == "");

    NormalizeGirEvidenceInputs(m);
    assert(Main(m).blocks[3].insts[0].a == 5);
    assert(Main(m).blocks[3].insts[1].a == 6);
    ProposeGirEvidence(m);
    assert(Main(m).blocks[4].insts[0].op == GirOp::Index);
    assert(Code(m) == "");
}

void EvidenceDropsAddressesAcrossScopeReentry() {
    auto m = Base();
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType array;
    array.kind = CoreType::Arr;
    array.elem = i64;
    array.count = 1;
    auto arrayType = m.Intern(array);
    Main(m).scopes = { -1, 0 };
    Main(m).slots = { { arrayType, CoreVarKind::Var, 1, 0 } };
    Main(m).summary.unknown = true;
    auto firstLiteral = Def(GirOp::Arr, 1);
    firstLiteral.ty = arrayType;
    firstLiteral.vals = { 0 };
    auto firstAddress = Def(GirOp::Slot, 2);
    firstAddress.idx = 0;
    auto length = Def(GirOp::ArrayLen, 3);
    length.a = 2;
    auto secondLiteral = Def(GirOp::Arr, 5);
    secondLiteral.ty = arrayType;
    secondLiteral.vals = { 4 };
    auto secondAddress = Def(GirOp::Slot, 6);
    secondAddress.idx = 0;
    auto view = Def(GirOp::Snap, 7);
    view.snap = GirSnapshotMode::Owner;
    view.a = 6;
    GirBlock entry;
    entry.insts = { Enter(0), Enter(1), Int(m, 0, "0"), firstLiteral, Init(0, 1), firstAddress,
                    length, Leave(1), Enter(1), Int(m, 4, "1"), secondLiteral, Init(0, 5),
                    secondAddress, view, Leave(1), Leave(0), Ret() };
    Main(m).blocks = { std::move(entry) };
    assert(Code(m) == "");

    NormalizeGirEvidenceInputs(m);
    assert(Main(m).blocks[0].insts[13].a == 6);
    assert(Code(m) == "");
}

void NonI64ComparisonDoesNotProveIndex() {
    auto m = Base();
    auto i64 = m.IntType(CoreIntTy::I64);
    auto u64 = m.IntType(CoreIntTy::U64);
    CoreType array;
    array.kind = CoreType::Arr;
    array.elem = i64;
    array.count = 1;
    auto arrayType = m.Intern(array);
    Main(m).slots = { { arrayType, CoreVarKind::Var, 0, 0 } };
    Main(m).summary.unknown = true;
    auto indexValue = Int(m, 0, "0");
    auto candidate = Int(m, 1, "0");
    candidate.ty = u64;
    auto limit = Int(m, 2, "4");
    limit.ty = u64;
    auto literal = Def(GirOp::Arr, 3);
    literal.ty = arrayType;
    literal.vals = { 0 };
    auto owner = Def(GirOp::Slot, 4);
    owner.idx = 0;
    auto length = Def(GirOp::ArrayLen, 5);
    length.a = 4;
    auto view = Def(GirOp::Snap, 6);
    view.snap = GirSnapshotMode::Owner;
    view.a = 4;
    auto within = Def(GirOp::Cmp, 7);
    within.cmp = CoreCmpOp::Lt;
    within.ty = u64;
    within.a = 1;
    within.b = 2;
    GirBlock entry;
    entry.insts = { Enter(0), indexValue, candidate, limit, literal, Init(0, 3), owner, length, view,
                    within, CondBr(7, 1, 2) };
    auto index = Def(GirOp::Index, 8);
    index.a = 6;
    index.b = 0;
    index.org = 0;
    auto load = Def(GirOp::Load, 9);
    load.a = 8;
    GirBlock success;
    success.insts = { index, load, Leave(0), Ret() };
    GirBlock failure;
    failure.insts = { Leave(0), Ret() };
    Main(m).blocks = { std::move(entry), std::move(success), std::move(failure) };
    assert(Code(m) == "");

    NormalizeGirEvidenceInputs(m);
    assert(Main(m).blocks[1].insts[0].b == 0);
    ProposeGirEvidence(m);
    assert(Main(m).blocks[1].insts[0].op == GirOp::Index);
    assert(Code(m) == "");
}

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

CoreModule CoreLengthModule(CoreType::Kind kind) {
    CoreModule core;
    core.profile = CoreProfile::Construction;
    core.files = { "length.goose" };
    auto i64 = core.IntType(CoreIntTy::I64);
    CoreType array;
    array.kind = kind;
    array.elem = i64;
    if (kind == CoreType::Arr || kind == CoreType::Limited) array.count = 1;
    auto arrayType = core.Intern(array);
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Let };
    CoreImpl implementation;
    implementation.name = "main";
    implementation.vars = { CoreVar { "items", arrayType, CoreVarKind::Var, 0, origin } };
    implementation.body.scope = 0;
    auto literal = make_unique<CoreExpr>();
    literal->kind = CoreExprKind::Arr;
    literal->type = arrayType;
    literal->elems.push_back(CoreInt(i64, "7"));
    CoreStmt initialize;
    initialize.kind = CoreStmtKind::Let;
    initialize.var = 0;
    initialize.expr = std::move(literal);
    initialize.org = origin;
    implementation.body.stmts.push_back(std::move(initialize));
    auto length = make_unique<CoreExpr>();
    length->kind = CoreExprKind::Len;
    length->type = i64;
    length->view = CorePlaceView(CoreLocal(0));
    length->org = origin;
    CoreStmt evaluate;
    evaluate.kind = CoreStmtKind::Expr;
    evaluate.expr = std::move(length);
    evaluate.org = origin;
    implementation.body.stmts.push_back(std::move(evaluate));
    core.impls.push_back(std::move(implementation));
    core.contexts = { CoreContext { .impl = 0 } };
    core.entry = 0;
    return core;
}

void DirectOwnerLengthsUseArrayLength() {
    for (auto kind : { CoreType::Arr, CoreType::Grow, CoreType::GrowShrink, CoreType::Limited }) {
        auto core = CoreLengthModule(kind);
        auto high = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Let } },
            [](const CoreOrigin &) { return 0; }).Lower();
        assert(Code(high) == "");
        int arrayLengths = 0, snapshots = 0, viewLengths = 0;
        for (auto &block : high.funcs[0].blocks) for (auto &inst : block.insts) {
            arrayLengths += inst.op == GirOp::ArrayLen;
            snapshots += inst.op == GirOp::Snap;
            viewLengths += inst.op == GirOp::ViewLen;
        }
        assert(arrayLengths == 1 && snapshots == 0 && viewLengths == 0);
    }
    auto core = CoreLengthModule(CoreType::VarArr);
    auto high = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Let } },
        [](const CoreOrigin &) { return 0; }).Lower();
    assert(Code(high) == "");
    int arrayLengths = 0, snapshots = 0, viewLengths = 0;
    for (auto &block : high.funcs[0].blocks) for (auto &inst : block.insts) {
        arrayLengths += inst.op == GirOp::ArrayLen;
        snapshots += inst.op == GirOp::Snap;
        viewLengths += inst.op == GirOp::ViewLen;
    }
    assert(arrayLengths == 0 && snapshots == 1 && viewLengths == 1);
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

void SpecializedParameterSummariesNormalizeBothCoverageSides() {
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
    assert(Code(m) == "");
    m.funcs[1].summary.reads.clear();
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

void RejectsConstructionTargetsInLowModule() {
    auto m = LowBase();
    m.lowtargets = { GirLowTarget { { 0 }, {}, {} } };
    assert(Code(m) == "GIR-V090");
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

// Write a global owner's header and stack through the low hidden result slot.
void StoreGlobalOwnerPair(GirModule &m, GirBlock &block, int firstValue,
                          int headerGlobal, int stackGlobal) {
    auto ptr = m.PtrType();
    auto header = Def(GirOp::GlobalAddr, firstValue);
    header.idx = headerGlobal;
    auto stack = Def(GirOp::GlobalStack, firstValue + 1);
    stack.idx = stackGlobal;
    block.insts.push_back(header);
    block.insts.push_back(stack);

    block.insts.push_back(Int(m, firstValue + 2, "0"));
    auto headerAddress = Def(GirOp::PtrOffset, firstValue + 3);
    headerAddress.idx = 8;
    headerAddress.a = 1;
    headerAddress.b = firstValue + 2;
    block.insts.push_back(headerAddress);
    GirInst storeHeader;
    storeHeader.op = GirOp::PStore;
    storeHeader.ty = ptr;
    storeHeader.a = firstValue + 3;
    storeHeader.b = firstValue;
    block.insts.push_back(storeHeader);

    block.insts.push_back(Int(m, firstValue + 4, "1"));
    auto stackAddress = Def(GirOp::PtrOffset, firstValue + 5);
    stackAddress.idx = 8;
    stackAddress.a = 1;
    stackAddress.b = firstValue + 4;
    block.insts.push_back(stackAddress);
    GirInst storeStack;
    storeStack.op = GirOp::PStore;
    storeStack.ty = ptr;
    storeStack.a = firstValue + 5;
    storeStack.b = firstValue + 1;
    block.insts.push_back(storeStack);
}

GirModule LowReturnedOwnerPairModule() {
    auto m = LowBase();
    auto ptr = m.PtrType();
    for (auto name : { "first", "second" }) {
        GirLowGlobal global;
        global.name = name;
        global.kind = GirMember::Header;
        m.lowglobals.push_back(global);
    }
    GirMember result;
    result.kind = GirMember::Bytes;
    result.size = 16;
    result.scope = 0;
    result.name = "result";
    Main(m).members = { result };

    GirFunc owner;
    owner.name = "owner";
    owner.params = { m.IntType(CoreIntTy::I64), ptr };
    owner.scopes = { -1 };
    owner.summary.unknown = true;
    GirBlock ownerEntry;
    ownerEntry.params = { { 0, owner.params[0] }, { 1, ptr } };
    StoreGlobalOwnerPair(m, ownerEntry, 2, 0, 0);
    ownerEntry.insts.push_back(Ret());
    owner.blocks = { ownerEntry };
    m.funcs.push_back(owner);

    GirInst resultAddress = Def(GirOp::FrameAddr, 1);
    resultAddress.idx = 0;
    GirInst call;
    call.op = GirOp::Call;
    call.idx = 1;
    call.vals = { 0, 1 };
    call.org = 0;
    GirBlock main;
    main.params = { { 0, m.IntType(CoreIntTy::I64) } };
    main.insts = { resultAddress, call };
    main.insts.push_back(Int(m, 2, "0"));
    auto headerAddress = Def(GirOp::PtrOffset, 3);
    headerAddress.idx = 8;
    headerAddress.a = 1;
    headerAddress.b = 2;
    main.insts.push_back(headerAddress);
    auto header = Def(GirOp::PLoad, 4);
    header.ty = ptr;
    header.a = 3;
    main.insts.push_back(header);
    main.insts.push_back(Int(m, 5, "1"));
    auto stackAddress = Def(GirOp::PtrOffset, 6);
    stackAddress.idx = 8;
    stackAddress.a = 1;
    stackAddress.b = 5;
    main.insts.push_back(stackAddress);
    auto stack = Def(GirOp::PLoad, 7);
    stack.ty = ptr;
    stack.a = 6;
    main.insts.push_back(stack);
    auto mark = Def(GirOp::HdrBase, 8);
    mark.a = 4;
    main.insts.push_back(mark);
    GirInst release;
    release.op = GirOp::StackRelease;
    release.a = 7;
    release.b = 8;
    main.insts.push_back(release);
    main.insts.push_back(Ret());
    Main(m).blocks = { main };
    return m;
}

void OwnerCallUsesReturnedPairOnlyAfterOneProvenCall() {
    auto m = LowReturnedOwnerPairModule();
    assert(Code(m) == "");

    // The output buffer is not a result of a call that happens later.
    auto beforeCall = LowReturnedOwnerPairModule();
    auto &instructions = Main(beforeCall).blocks[0].insts;
    auto call = std::find_if(instructions.begin(), instructions.end(),
                             [](const GirInst &i) { return i.op == GirOp::Call; });
    assert(call != instructions.end());
    auto savedCall = *call;
    instructions.erase(call);
    auto headerBase = std::find_if(instructions.begin(), instructions.end(),
                                   [](const GirInst &i) { return i.op == GirOp::HdrBase; });
    instructions.insert(headerBase, savedCall);
    assert(Code(beforeCall) == "GIR-V090");

    // An intervening pointer store can overwrite the returned header.
    auto overwritten = LowReturnedOwnerPairModule();
    auto &overwrittenInstructions = Main(overwritten).blocks[0].insts;
    auto outputCall = std::find_if(overwrittenInstructions.begin(), overwrittenInstructions.end(),
                                   [](const GirInst &i) { return i.op == GirOp::Call; });
    assert(outputCall != overwrittenInstructions.end());
    auto global = Def(GirOp::GlobalAddr, 9);
    global.idx = 1;
    GirInst store;
    store.op = GirOp::PStore;
    store.ty = overwritten.PtrType();
    store.a = 1;
    store.b = 9;
    outputCall = overwrittenInstructions.insert(outputCall + 1, global);
    overwrittenInstructions.insert(outputCall + 1, store);
    assert(Code(overwritten) == "GIR-V090");

    // Reusing one frame slot for two calls leaves the loads ambiguous.
    auto reused = LowReturnedOwnerPairModule();
    auto &reusedInstructions = Main(reused).blocks[0].insts;
    auto firstCall = std::find_if(reusedInstructions.begin(), reusedInstructions.end(),
                                  [](const GirInst &i) { return i.op == GirOp::Call; });
    auto secondCall = *firstCall;
    reusedInstructions.insert(firstCall + 1, secondCall);
    assert(Code(reused) == "GIR-V090");
}

void ReturnedOwnerPairRequiresEveryReturnAndMatchingStores() {
    auto missing = LowReturnedOwnerPairModule();
    auto &owner = missing.funcs[1];
    GirBlock entry;
    entry.params = owner.blocks[0].params;
    auto cond = Def(GirOp::Bool, 2);
    entry.insts.push_back(cond);
    GirInst branch;
    branch.op = GirOp::CondBr;
    branch.a = 2;
    branch.idx = 1;
    branch.idx2 = 2;
    entry.insts.push_back(branch);
    GirBlock good;
    StoreGlobalOwnerPair(missing, good, 3, 0, 0);
    good.insts.push_back(Ret());
    GirBlock missingStores;
    missingStores.insts = { Ret() };
    owner.blocks = { entry, good, missingStores };
    assert(Code(missing) == "GIR-V090");

    // Matching pointer types alone do not establish a header/stack pair.
    auto mismatch = LowReturnedOwnerPairModule();
    auto &stores = mismatch.funcs[1].blocks[0].insts;
    auto stack = std::find_if(stores.begin(), stores.end(), [](const GirInst &i) {
        return i.op == GirOp::GlobalStack;
    });
    assert(stack != stores.end());
    stack->idx = 1;
    assert(Code(mismatch) == "GIR-V090");
}

void ReturnedOwnerPairRejectsUnsafePhiCycles() {
    auto m = LowReturnedOwnerPairModule();
    auto &owner = m.funcs[1];
    auto ptr = m.PtrType();
    GirMember headerMember;
    headerMember.kind = GirMember::Header;
    headerMember.scope = 0;
    headerMember.stack = 0;
    owner.members = { headerMember };
    owner.stacks = 1;

    GirBlock entry;
    entry.params = owner.blocks[0].params;
    auto cond = Def(GirOp::Bool, 2);
    auto globalHeader = Def(GirOp::GlobalAddr, 3);
    globalHeader.idx = 0;
    auto globalStack = Def(GirOp::GlobalStack, 4);
    globalStack.idx = 0;
    auto localHeader = Def(GirOp::FrameAddr, 5);
    localHeader.idx = 0;
    auto localStack = Def(GirOp::StackAt, 6);
    localStack.a = 0;
    localStack.idx = 0;
    GirInst choose;
    choose.op = GirOp::CondBr;
    choose.a = 2;
    choose.idx = 1;
    choose.idx2 = 2;
    entry.insts = { cond, globalHeader, globalStack, localHeader, localStack, choose };

    GirBlock safe;
    safe.insts = { Br(4, { 3, 4 }) };
    GirBlock local;
    local.insts = { Br(3, { 5, 6 }) };
    GirBlock loop;
    loop.params = { { 7, ptr }, { 8, ptr } };
    auto loopAgain = Def(GirOp::Bool, 9);
    GirInst loopBranch;
    loopBranch.op = GirOp::CondBr;
    loopBranch.a = 9;
    loopBranch.idx = 4;
    loopBranch.vals = { 7, 8 };
    loopBranch.idx2 = 3;
    loopBranch.vals2 = { 7, 8 };
    loop.insts = { loopAgain, loopBranch };

    GirBlock join;
    join.params = { { 10, ptr }, { 11, ptr } };
    // Store the joined pair using the output ABI from the normal return block.
    join.insts.push_back(Int(m, 12, "0"));
    auto headerAddress = Def(GirOp::PtrOffset, 13);
    headerAddress.idx = 8;
    headerAddress.a = 1;
    headerAddress.b = 12;
    GirInst storeHeader;
    storeHeader.op = GirOp::PStore;
    storeHeader.ty = ptr;
    storeHeader.a = 13;
    storeHeader.b = 10;
    join.insts.push_back(headerAddress);
    join.insts.push_back(storeHeader);
    join.insts.push_back(Int(m, 14, "1"));
    auto stackAddress = Def(GirOp::PtrOffset, 15);
    stackAddress.idx = 8;
    stackAddress.a = 1;
    stackAddress.b = 14;
    GirInst storeStack;
    storeStack.op = GirOp::PStore;
    storeStack.ty = ptr;
    storeStack.a = 15;
    storeStack.b = 11;
    join.insts.push_back(stackAddress);
    join.insts.push_back(storeStack);
    join.insts.push_back(Ret());
    owner.blocks = { entry, safe, local, loop, join };
    assert(Code(m) == "GIR-V090");
}

void RecursiveOwnerReturnDoesNotSeedItsOwnProof() {
    auto m = LowReturnedOwnerPairModule();
    auto &owner = m.funcs[1];
    GirMember result;
    result.kind = GirMember::Bytes;
    result.size = 16;
    result.scope = 0;
    owner.members = { result };
    GirBlock entry;
    entry.params = owner.blocks[0].params;
    entry.insts = { Def(GirOp::Bool, 2) };
    GirInst choose;
    choose.op = GirOp::CondBr;
    choose.a = 2;
    choose.idx = 1;
    choose.idx2 = 2;
    entry.insts.push_back(choose);
    GirBlock base;
    StoreGlobalOwnerPair(m, base, 3, 0, 0);
    base.insts.push_back(Ret());
    GirBlock recursive;
    auto buffer = Def(GirOp::FrameAddr, 9);
    buffer.idx = 0;
    GirInst call;
    call.op = GirOp::Call;
    call.idx = 1;
    call.vals = { 0, 9 };
    call.org = 0;
    recursive.insts = { buffer, call };
    recursive.insts.push_back(Int(m, 10, "0"));
    auto headerAddress = Def(GirOp::PtrOffset, 11);
    headerAddress.idx = 8;
    headerAddress.a = 9;
    headerAddress.b = 10;
    auto header = Def(GirOp::PLoad, 12);
    header.ty = m.PtrType();
    header.a = 11;
    recursive.insts.push_back(headerAddress);
    recursive.insts.push_back(header);
    recursive.insts.push_back(Int(m, 13, "1"));
    auto stackAddress = Def(GirOp::PtrOffset, 14);
    stackAddress.idx = 8;
    stackAddress.a = 9;
    stackAddress.b = 13;
    auto stack = Def(GirOp::PLoad, 15);
    stack.ty = m.PtrType();
    stack.a = 14;
    recursive.insts.push_back(stackAddress);
    recursive.insts.push_back(stack);
    recursive.insts.push_back(Int(m, 16, "0"));
    auto outputHeader = Def(GirOp::PtrOffset, 17);
    outputHeader.idx = 8;
    outputHeader.a = 1;
    outputHeader.b = 16;
    GirInst storeHeader;
    storeHeader.op = GirOp::PStore;
    storeHeader.ty = m.PtrType();
    storeHeader.a = 17;
    storeHeader.b = 12;
    recursive.insts.push_back(outputHeader);
    recursive.insts.push_back(storeHeader);
    recursive.insts.push_back(Int(m, 18, "1"));
    auto outputStack = Def(GirOp::PtrOffset, 19);
    outputStack.idx = 8;
    outputStack.a = 1;
    outputStack.b = 18;
    GirInst storeStack;
    storeStack.op = GirOp::PStore;
    storeStack.ty = m.PtrType();
    storeStack.a = 19;
    storeStack.b = 15;
    recursive.insts.push_back(outputStack);
    recursive.insts.push_back(storeStack);
    recursive.insts.push_back(Ret());
    owner.blocks = { entry, base, recursive };
    assert(Code(m) == "GIR-V090");
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

GirModule ShrinkReplaceRunThroughPhi() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::GrowShrink;
    owner.elem = i64;
    auto ownerTy = m.Intern(owner);
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    Main(m).slots = { { ownerTy, CoreVarKind::Var, 0, 0 } };
    Main(m).summary.unknown = true;

    auto empty = Def(GirOp::Arr, 0);
    empty.ty = ownerTy;
    auto init = Init(0, 0);
    auto slot = Def(GirOp::Slot, 1);
    slot.idx = 0;
    slot.ty = refTy;
    GirInst clear;
    clear.op = GirOp::Clear;
    clear.a = 1;
    clear.org = 0;
    auto condition = Def(GirOp::Bool, 2);
    condition.flag = true;
    Main(m).blocks[0].insts = { Enter(0), empty, init, slot, clear, condition, CondBr(2, 1, 2) };

    GirBlock shorter, longer, join;
    auto first = Int(m, 3, "40");
    auto shortRun = Def(GirOp::Arr, 4);
    shortRun.ty = ownerTy;
    shortRun.vals = { 3 };
    shorter.insts = { first, shortRun, Br(3, { 4 }) };

    auto second = Int(m, 5, "50");
    auto third = Int(m, 6, "60");
    auto longRun = Def(GirOp::Arr, 7);
    longRun.ty = ownerTy;
    longRun.vals = { 5, 6 };
    longer.insts = { second, third, longRun, Br(3, { 7 }) };

    join.params = { { 8, ownerTy } };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 1;
    replace.b = 8;
    replace.org = 0;
    join.insts = { replace, Leave(0), Ret() };
    Main(m).blocks = { Main(m).blocks[0], shorter, longer, join };
    return m;
}

void LowPreservesOwnerLiteralRunsAcrossJoins() {
    // Replacing from either literal arm must publish that arm's run length;
    // the old lowering silently treated the owner block parameter as empty.
    auto high = ShrinkReplaceRunThroughPhi();
    assert(Code(high) == "");
    auto low = GirToLow(high).Lower();
    assert(!GirVerifier(low).Verify());

    bool copiesSelectedRun = false;
    bool replacementUsesSelectedLength = false;
    int lengthMember = -1;
    for (auto &block : low.funcs[0].blocks) {
        for (auto &inst : block.insts) copiesSelectedRun |= inst.op == GirOp::BytesCopy;
        for (auto &inst : block.insts) {
            if (inst.op != GirOp::HdrSetLen) continue;
            for (auto &definition : block.insts)
                if (definition.op == GirOp::LocalGet && definition.res == inst.b) {
                    replacementUsesSelectedLength = true;
                    lengthMember = definition.idx;
                }
        }
    }
    auto lengthWrites = 0;
    bool hasLengthOne = false;
    bool hasLengthTwo = false;
    for (auto &block : low.funcs[0].blocks)
        for (auto &inst : block.insts) {
            if (inst.op != GirOp::LocalSet || inst.idx != lengthMember) continue;
            lengthWrites++;
            for (auto &definitionBlock : low.funcs[0].blocks)
                for (auto &definition : definitionBlock.insts)
                    if (definition.op == GirOp::Int && definition.res == inst.a) {
                        hasLengthOne |= definition.text == "1";
                        hasLengthTwo |= definition.text == "2";
                    }
        }
    assert(copiesSelectedRun);
    assert(replacementUsesSelectedLength);
    assert(lengthWrites == 2);
    assert(hasLengthOne && hasLengthTwo);
}

GirModule ShrinkReplaceRunThroughSameTargetCondBr(bool selectShort) {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::GrowShrink;
    owner.elem = i64;
    auto ownerTy = m.Intern(owner);
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    Main(m).slots = { { ownerTy, CoreVarKind::Var, 0, 0 } };
    Main(m).summary.unknown = true;

    auto empty = Def(GirOp::Arr, 0);
    empty.ty = ownerTy;
    auto init = Init(0, 0);
    auto slot = Def(GirOp::Slot, 1);
    slot.idx = 0;
    slot.ty = refTy;
    GirInst clear;
    clear.op = GirOp::Clear;
    clear.a = 1;
    clear.org = 0;
    auto condition = Def(GirOp::Bool, 2);
    condition.flag = selectShort;
    auto first = Int(m, 3, "40");
    auto shortRun = Def(GirOp::Arr, 4);
    shortRun.ty = ownerTy;
    shortRun.vals = { 3 };
    auto second = Int(m, 5, "50");
    auto third = Int(m, 6, "60");
    auto longRun = Def(GirOp::Arr, 7);
    longRun.ty = ownerTy;
    longRun.vals = { 5, 6 };
    GirInst branch;
    branch.op = GirOp::CondBr;
    branch.a = 2;
    branch.idx = 1;
    branch.idx2 = 1;
    branch.vals = { 4 };
    branch.vals2 = { 7 };
    Main(m).blocks[0].insts = {
        Enter(0), empty, init, slot, clear, condition, first, shortRun,
        second, third, longRun, branch,
    };

    GirBlock join;
    join.params = { { 8, ownerTy } };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 1;
    replace.b = 8;
    replace.org = 0;
    GirInst length = Def(GirOp::ArrayLen, 9);
    length.a = 1;
    GirInst snapshot = Def(GirOp::Snap, 10);
    snapshot.a = 1;
    snapshot.snap = GirSnapshotMode::Owner;
    auto zero = Int(m, 11, "0");
    GirInst firstElement = Def(GirOp::Index, 12);
    firstElement.a = 10;
    firstElement.b = 11;
    firstElement.org = 0;
    GirInst load = Def(GirOp::Load, 13);
    load.a = 12;
    GirInst print;
    print.op = GirOp::Print;
    print.parts = { { false, "", 9 }, { true, " ", 0 }, { false, "", 13 } };
    print.org = 0;
    join.insts = { replace, length, snapshot, zero, firstElement, load, print, Leave(0), Ret() };
    Main(m).blocks.push_back(join);
    return m;
}

void LowSplitsSameTargetCondBrForOwnerRuns() {
    for (auto selectShort : { false, true }) {
        auto high = ShrinkReplaceRunThroughSameTargetCondBr(selectShort);
        assert(Code(high) == "");
        auto low = GirToLow(high).Lower();
        assert(!GirVerifier(low).Verify());
        bool routedThroughDistinctEdges = false;
        for (auto &block : low.funcs[0].blocks)
            for (auto &inst : block.insts)
                if (inst.op == GirOp::CondBr && inst.idx != inst.idx2)
                    routedThroughDistinctEdges = true;
        assert(routedThroughDistinctEdges);
    }
}

GirModule ShrinkReplaceReceiverViaSlotLoad() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::GrowShrink;
    owner.elem = i64;
    auto ownerTy = m.Intern(owner);
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    Main(m).slots = { { ownerTy, CoreVarKind::Var, 0, 0 }, { i64, CoreVarKind::Var, 0, 1 } };
    Main(m).summary.unknown = true;

    auto initial = Def(GirOp::Arr, 0);
    initial.ty = ownerTy;
    auto ownerInit = Init(0, 0);
    auto ownerRef = Def(GirOp::Slot, 1);
    ownerRef.idx = 0;
    ownerRef.ty = refTy;
    auto savedLength = Def(GirOp::ArrayLen, 2);
    savedLength.a = 1;
    auto scalarInit = Init(1, 2);
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 1;
    clear.org = 0;
    auto scalarRef = Def(GirOp::Slot, 3);
    scalarRef.idx = 1;
    auto savedLengthLoad = Def(GirOp::Load, 4);
    savedLengthLoad.a = 3;
    auto run = Def(GirOp::Arr, 5);
    run.ty = ownerTy;
    run.vals = { 4 };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 1;
    replace.b = 5;
    replace.org = 0;
    Main(m).blocks[0].insts = {
        Enter(0), initial, ownerInit, ownerRef, savedLength, scalarInit, clear,
        scalarRef, savedLengthLoad, run, replace, Leave(0), Ret(),
    };
    return m;
}

GirModule ShrinkReplaceFromSavedElement() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    Main(m).slots = { { ownerTy, CoreVarKind::Var, 0, 0 } };
    Main(m).summary.unknown = true;

    auto value = Int(m, 0, "7");
    auto initial = Def(GirOp::Arr, 1);
    initial.ty = ownerTy;
    initial.vals = { 0 };
    auto ownerInit = Init(0, 1);
    auto ownerRef = Def(GirOp::Slot, 2);
    ownerRef.idx = 0;
    ownerRef.ty = refTy;
    auto snapshot = Def(GirOp::Snap, 3);
    snapshot.a = 2;
    snapshot.snap = GirSnapshotMode::Owner;
    auto zero = Int(m, 4, "0");
    auto element = Def(GirOp::Index, 5);
    element.a = 3;
    element.b = 4;
    element.org = 0;
    auto saved = Def(GirOp::Load, 6);
    saved.a = 5;
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 2;
    clear.org = 0;
    auto run = Def(GirOp::Arr, 7);
    run.ty = ownerTy;
    run.vals = { 6 };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 2;
    replace.b = 7;
    replace.org = 0;
    Main(m).blocks[0].insts = { Enter(0), value, initial, ownerInit, ownerRef, snapshot,
                                zero, element, saved, clear, run, replace, Leave(0), Ret() };
    return m;
}

GirModule ShrinkReplaceAfterDiscardedSlotAddress() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    Main(m).slots = { { ownerTy, CoreVarKind::Var, 0, 0 } };
    Main(m).summary.unknown = true;

    auto initial = Def(GirOp::Arr, 0);
    initial.ty = ownerTy;
    auto ownerInit = Init(0, 0);
    auto ownerRef = Def(GirOp::Slot, 1);
    ownerRef.idx = 0;
    ownerRef.ty = refTy;
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 1;
    clear.org = 0;
    auto discardedAlias = Def(GirOp::Slot, 2);
    discardedAlias.idx = 0;
    discardedAlias.ty = refTy;
    auto run = Def(GirOp::Arr, 3);
    run.ty = ownerTy;
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 1;
    replace.b = 3;
    replace.org = 0;
    Main(m).blocks[0].insts = { Enter(0), initial, ownerInit, ownerRef, clear,
                                discardedAlias, run, replace, Leave(0), Ret() };
    return m;
}

GirModule ShrinkBranchConditionSelectsRun() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    GirFunc branch;
    branch.name = "branch-dependent-run";
    branch.params = { refTy };
    branch.scopes = { -1 };
    branch.summary.unknown = true;

    GirBlock entry;
    entry.params = { { 0, refTy } };
    auto length = Def(GirOp::ArrayLen, 1);
    length.a = 0;
    auto zero = Int(m, 2, "0");
    auto condition = Def(GirOp::Cmp, 3);
    condition.ty = i64;
    condition.a = 1;
    condition.b = 2;
    condition.cmp = CoreCmpOp::Eq;
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 0;
    clear.org = 0;
    entry.insts = { length, zero, condition, clear, CondBr(3, 1, 2) };

    GirBlock left, right, join;
    auto leftValue = Int(m, 4, "10");
    auto leftRun = Def(GirOp::Arr, 5);
    leftRun.ty = ownerTy;
    leftRun.vals = { 4 };
    left.insts = { leftValue, leftRun, Br(3, { 5 }) };
    auto rightValue = Int(m, 6, "20");
    auto rightRun = Def(GirOp::Arr, 7);
    rightRun.ty = ownerTy;
    rightRun.vals = { 6 };
    right.insts = { rightValue, rightRun, Br(3, { 7 }) };
    join.params = { { 8, ownerTy } };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 0;
    replace.b = 8;
    replace.org = 0;
    join.insts = { replace, Ret() };
    branch.blocks = { entry, left, right, join };
    m.funcs.push_back(std::move(branch));
    return m;
}

GirModule ShrinkCallResultReadsGlobalBeforeReplace(bool unknownSummary) {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);

    GirGlobal source;
    source.name = "source";
    source.ty = i64;
    source.kind = CoreVarKind::Var;
    source.init.name = "source-init";
    source.init.results = { i64 };
    source.init.summary.unknown = true;
    GirBlock init;
    init.insts = { Int(m, 0, "0"), Ret({ 0 }) };
    source.init.blocks = { init };
    m.globals.push_back(source);

    GirFunc caller;
    caller.name = "call-dependent-run";
    caller.params = { refTy };
    caller.scopes = { -1 };
    caller.summary.unknown = true;
    GirBlock callerBlock;
    callerBlock.params = { { 0, refTy } };
    auto result = Def(GirOp::Call, 1);
    result.idx = 2;
    result.org = 0;
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 0;
    clear.org = 0;
    auto run = Def(GirOp::Arr, 2);
    run.ty = ownerTy;
    run.vals = { 1 };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 0;
    replace.b = 2;
    replace.org = 0;
    callerBlock.insts = { result, clear, run, replace, Ret() };
    caller.blocks = { callerBlock };

    GirFunc reader;
    reader.name = unknownSummary ? "unknown-reader" : "global-reader";
    reader.results = { i64 };
    reader.scopes = { -1 };
    GirBlock readerBlock;
    if (unknownSummary) {
        reader.summary.unknown = true;
        readerBlock.insts = { Int(m, 0, "0"), Ret({ 0 }) };
    } else {
        auto global = Def(GirOp::Global, 0);
        global.idx = 0;
        auto load = Def(GirOp::Load, 1);
        load.a = 0;
        reader.summary.reads = { CoreTarget { true, 0 } };
        readerBlock.insts = { global, load, Ret({ 1 }) };
    }
    reader.blocks = { readerBlock };
    m.funcs.push_back(std::move(caller));
    m.funcs.push_back(std::move(reader));
    return m;
}

GirModule ShrinkCallSummaryInvalidatesReplace(int effect) {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);

    GirFunc caller;
    caller.name = "call-invalidates-empty-owner";
    bool aliasActual = effect == 6;
    bool unrelatedLocalActual = effect == 7;
    caller.params = aliasActual ? vector<GirTypeId> { refTy, refTy } : vector<GirTypeId> { refTy };
    caller.scopes = { -1 };
    if (unrelatedLocalActual) caller.slots = { { ownerTy, CoreVarKind::Var, 0, 0 } };
    caller.summary.unknown = true;
    GirBlock body;
    body.params = aliasActual ? vector<pair<int, GirTypeId>> { { 0, refTy }, { 1, refTy } }
                              : vector<pair<int, GirTypeId>> { { 0, refTy } };
    if (unrelatedLocalActual) {
        auto localRun = Def(GirOp::Arr, 1);
        localRun.ty = ownerTy;
        auto localInit = Init(0, 1);
        auto localRef = Def(GirOp::Slot, 2);
        localRef.idx = 0;
        localRef.ty = refTy;
        body.insts = { Enter(0), localRun, localInit, localRef };
    }
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 0;
    clear.org = 0;
    GirInst call;
    call.op = GirOp::Call;
    call.idx = 2;
    call.vals = { unrelatedLocalActual ? 2 : aliasActual ? 1 : 0 };
    call.org = 0;
    auto valueId = unrelatedLocalActual ? 3 : aliasActual ? 2 : 1;
    auto value = Int(m, valueId, "7");
    auto run = Def(GirOp::Arr, valueId + 1);
    run.ty = ownerTy;
    run.vals = { value.res };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 0;
    replace.b = run.res;
    replace.org = 0;
    body.insts.insert(body.insts.end(), { clear, call, value, run, replace });
    if (unrelatedLocalActual) body.insts.push_back(Leave(0));
    body.insts.push_back(Ret());
    caller.blocks = { body };

    GirFunc touch;
    touch.name = "touch-owner";
    touch.params = { refTy };
    touch.scopes = { -1 };
    touch.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    if (effect == 5) touch.summary.unknown = true;
    CoreTarget target { false, 0 };
    if (effect == 0) touch.summary.reads = { target };
    if (effect == 1) touch.summary.shrinks = { target };
    if (effect == 2) touch.summary.writes = { target };
    if (effect == 3) touch.summary.grows = { target };
    if (effect == 4) touch.summary.rebinds = { target };
    GirBlock touchBlock;
    touchBlock.params = { { 0, refTy } };
    touchBlock.insts = { Ret() };
    touch.blocks = { touchBlock };
    m.funcs.push_back(std::move(caller));
    m.funcs.push_back(std::move(touch));
    return m;
}

GirModule ShrinkLocalReplacementWithUnrelatedParameterRead() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);

    GirFunc caller;
    caller.name = "local-owner-unrelated-parameter-read";
    caller.params = { refTy };
    caller.slots = { { ownerTy, CoreVarKind::Var, 0, 0 } };
    caller.scopes = { -1 };
    caller.summary.unknown = true;
    GirBlock callerBlock;
    callerBlock.params = { { 0, refTy } };
    auto empty = Def(GirOp::Arr, 1);
    empty.ty = ownerTy;
    auto init = Init(0, 1);
    auto owner = Def(GirOp::Slot, 2);
    owner.idx = 0;
    owner.ty = refTy;
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 2;
    clear.org = 0;
    auto call = Def(GirOp::Call, 3);
    call.idx = 2;
    call.vals = { 0 };
    call.org = 0;
    auto run = Def(GirOp::Arr, 4);
    run.ty = ownerTy;
    run.vals = { 3 };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 2;
    replace.b = 4;
    replace.org = 0;
    callerBlock.insts = { Enter(0), empty, init, owner, clear, call, run,
                          replace, Leave(0), Ret() };
    caller.blocks = { callerBlock };

    GirFunc reader;
    reader.name = "read-unrelated-owner";
    reader.params = { refTy };
    reader.results = { i64 };
    reader.scopes = { -1 };
    reader.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    reader.summary.reads = { CoreTarget { false, 0 } };
    GirBlock readerBlock;
    readerBlock.params = { { 0, refTy } };
    readerBlock.insts = { Int(m, 1, "7"), Ret({ 1 }) };
    reader.blocks = { readerBlock };

    m.funcs.push_back(std::move(caller));
    m.funcs.push_back(std::move(reader));
    return m;
}

GirModule ShrinkReplaceAfterClearReadIntoRun(bool readElement) {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    GirFunc probe;
    probe.name = readElement ? "replace-after-clear-element-read" : "replace-after-clear-length-read";
    probe.params = { refTy };
    probe.scopes = { -1 };
    probe.summary.unknown = true;
    GirBlock body;
    body.params = { { 0, refTy } };
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 0;
    clear.org = 0;
    body.insts.push_back(clear);
    int element = -1;
    if (readElement) {
        auto snapshot = Def(GirOp::Snap, 1);
        snapshot.a = 0;
        snapshot.snap = GirSnapshotMode::Owner;
        auto zero = Int(m, 2, "0");
        auto index = Def(GirOp::Index, 3);
        index.a = 1;
        index.b = 2;
        index.org = 0;
        auto load = Def(GirOp::Load, 4);
        load.a = 3;
        body.insts.insert(body.insts.end(), { snapshot, zero, index, load });
        element = 4;
    } else {
        auto length = Def(GirOp::ArrayLen, 1);
        length.a = 0;
        body.insts.push_back(length);
        element = 1;
    }
    auto runId = readElement ? 5 : 2;
    auto run = Def(GirOp::Arr, runId);
    run.ty = ownerTy;
    run.vals = { element };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 0;
    replace.b = runId;
    replace.org = 0;
    body.insts.push_back(run);
    body.insts.push_back(replace);
    body.insts.push_back(Ret());
    probe.blocks = { body };
    m.funcs.push_back(std::move(probe));
    return m;
}

GirModule ShrinkReplaceAfterAppendSourceAlias() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    GirFunc probe;
    probe.name = "replace-after-append-source-alias";
    probe.params = { refTy };
    probe.slots = { { ownerTy, CoreVarKind::Var, 0, 0 } };
    probe.scopes = { -1 };
    probe.summary.unknown = true;
    GirBlock body;
    body.params = { { 0, refTy } };
    auto empty = Def(GirOp::Arr, 1);
    empty.ty = ownerTy;
    auto init = Init(0, 1);
    auto appendTarget = Def(GirOp::Slot, 2);
    appendTarget.idx = 0;
    appendTarget.ty = refTy;
    auto sourceView = Def(GirOp::Snap, 3);
    sourceView.a = 0;
    sourceView.snap = GirSnapshotMode::Owner;
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 0;
    clear.org = 0;
    GirInst append;
    append.op = GirOp::Append;
    append.a = appendTarget.res;
    append.b = sourceView.res;
    append.org = 0;
    auto value = Int(m, 4, "7");
    auto run = Def(GirOp::Arr, 5);
    run.ty = ownerTy;
    run.vals = { value.res };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 0;
    replace.b = run.res;
    replace.org = 0;
    body.insts = { Enter(0), empty, init, appendTarget, sourceView, clear,
                   append, value, run, replace, Leave(0), Ret() };
    probe.blocks = { body };
    m.funcs.push_back(std::move(probe));
    return m;
}

GirModule ShrinkReplaceAfterSlotInitSourceAlias() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    GirFunc probe;
    probe.name = "replace-after-slot-init-source-alias";
    probe.params = { refTy };
    probe.slots = { { refTy, CoreVarKind::Var, 0, 0 } };
    probe.scopes = { -1 };
    probe.summary.unknown = true;
    GirBlock body;
    body.params = { { 0, refTy } };
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 0;
    clear.org = 0;
    auto slotInit = Init(0, 0);
    slotInit.org = 0;
    auto run = Def(GirOp::Arr, 1);
    run.ty = ownerTy;
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 0;
    replace.b = run.res;
    replace.org = 0;
    body.insts = { Enter(0), clear, slotInit, run, replace, Leave(0), Ret() };
    probe.blocks = { body };
    m.funcs.push_back(std::move(probe));
    return m;
}

enum class EmptyOwnerEffect : uint8_t {
    Load, Snapshot, Length, SliceView, ViewLength, ViewSlice, Index, Push, Pop, PopN, Resize,
    Store, Append, Replace,
};

GirModule ShrinkReplaceAfterAliasedEffect(EmptyOwnerEffect effect) {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    auto sliceTy = m.SliceType(CoreMut::Mut, i64);
    auto viewTy = m.ViewType(CoreMut::Mut, i64);

    GirFunc probe;
    probe.name = cat("empty-owner-effect-", (int)effect);
    probe.params = { refTy, sliceTy, viewTy };
    probe.scopes = { -1 };
    probe.summary.unknown = true;
    GirBlock body;
    body.params = { { 0, refTy }, { 1, sliceTy }, { 2, viewTy } };
    auto &insts = body.insts;
    int next = 3;
    auto intValue = [&](const char *text) {
        auto id = next++;
        insts.push_back(Int(m, id, text));
        return id;
    };
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 0;
    clear.org = 0;

    if (effect == EmptyOwnerEffect::Load) {
        // Hold an element address across clear so only the load can invalidate
        // the empty fact.
        auto snapshot = Def(GirOp::Snap, next++);
        snapshot.a = 0;
        snapshot.snap = GirSnapshotMode::Owner;
        auto zero = intValue("0");
        auto element = Def(GirOp::Index, next++);
        element.a = snapshot.res;
        element.b = zero;
        element.org = 0;
        insts.push_back(snapshot);
        insts.push_back(element);
        insts.push_back(clear);
        auto load = Def(GirOp::Load, next++);
        load.a = element.res;
        insts.push_back(load);
    } else {
        insts.push_back(clear);
        switch (effect) {
            case EmptyOwnerEffect::Snapshot: {
                auto snapshot = Def(GirOp::Snap, next++);
                snapshot.a = 0;
                snapshot.snap = GirSnapshotMode::Owner;
                insts.push_back(snapshot);
                break;
            }
            case EmptyOwnerEffect::Length: {
                auto length = Def(GirOp::ArrayLen, next++);
                length.a = 0;
                insts.push_back(length);
                break;
            }
            case EmptyOwnerEffect::SliceView: {
                auto view = Def(GirOp::SliceView, next++);
                view.a = 1;
                insts.push_back(view);
                break;
            }
            case EmptyOwnerEffect::ViewLength: {
                auto length = Def(GirOp::ViewLen, next++);
                length.a = 2;
                insts.push_back(length);
                break;
            }
            case EmptyOwnerEffect::ViewSlice: {
                auto slice = Def(GirOp::ViewSlice, next++);
                slice.a = 2;
                insts.push_back(slice);
                break;
            }
            case EmptyOwnerEffect::Index: {
                auto zero = intValue("0");
                auto index = Def(GirOp::Index, next++);
                index.a = 2;
                index.b = zero;
                index.org = 0;
                insts.push_back(index);
                break;
            }
            case EmptyOwnerEffect::Push: {
                auto value = intValue("7");
                auto push = Def(GirOp::Push, next++);
                push.a = 0;
                push.b = value;
                push.org = 0;
                insts.push_back(push);
                break;
            }
            case EmptyOwnerEffect::Pop: {
                auto pop = Def(GirOp::Pop, next++);
                pop.a = 0;
                pop.org = 0;
                insts.push_back(pop);
                break;
            }
            case EmptyOwnerEffect::PopN: {
                auto count = intValue("0");
                GirInst popn;
                popn.op = GirOp::PopN;
                popn.a = 0;
                popn.b = count;
                popn.org = 0;
                insts.push_back(popn);
                break;
            }
            case EmptyOwnerEffect::Resize: {
                auto count = intValue("0");
                GirInst resize;
                resize.op = GirOp::Resize;
                resize.a = 0;
                resize.b = count;
                resize.org = 0;
                insts.push_back(resize);
                break;
            }
            case EmptyOwnerEffect::Store: {
                auto zero = intValue("0");
                auto index = Def(GirOp::Index, next++);
                index.a = 2;
                index.b = zero;
                index.org = 0;
                insts.push_back(index);
                auto value = intValue("7");
                GirInst store;
                store.op = GirOp::Store;
                store.a = index.res;
                store.b = value;
                store.org = 0;
                insts.push_back(store);
                break;
            }
            case EmptyOwnerEffect::Append: {
                GirInst append;
                append.op = GirOp::Append;
                append.a = 0;
                append.b = 2;
                append.org = 0;
                insts.push_back(append);
                break;
            }
            case EmptyOwnerEffect::Replace: {
                auto firstValue = intValue("7");
                auto firstRun = Def(GirOp::Arr, next++);
                firstRun.ty = ownerTy;
                firstRun.vals = { firstValue };
                insts.push_back(firstRun);
                GirInst firstReplace;
                firstReplace.op = GirOp::Replace;
                firstReplace.a = 0;
                firstReplace.b = firstRun.res;
                firstReplace.org = 0;
                insts.push_back(firstReplace);
                break;
            }
            case EmptyOwnerEffect::Load: assert(false); break;
        }
    }

    auto replacementValue = intValue("8");
    auto run = Def(GirOp::Arr, next++);
    run.ty = ownerTy;
    run.vals = { replacementValue };
    insts.push_back(run);
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 0;
    replace.b = run.res;
    replace.org = 0;
    insts.push_back(replace);
    insts.push_back(Ret());
    probe.blocks = { body };
    m.funcs.push_back(std::move(probe));
    return m;
}

GirModule ShrinkReplaceClearedOnOneBranch() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);
    GirFunc probe;
    probe.name = "clear-only-on-one-branch";
    probe.params = { refTy };
    probe.scopes = { -1 };
    probe.summary.unknown = true;
    GirBlock entry, cleared, unchanged, join;
    entry.params = { { 0, refTy } };
    auto condition = Def(GirOp::Bool, 1);
    condition.flag = true;
    entry.insts = { condition, CondBr(1, 1, 2) };
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 0;
    clear.org = 0;
    cleared.insts = { clear, Br(3) };
    unchanged.insts = { Br(3) };
    auto value = Int(m, 2, "8");
    auto run = Def(GirOp::Arr, 3);
    run.ty = ownerTy;
    run.vals = { 2 };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 0;
    replace.b = 3;
    replace.org = 0;
    join.insts = { value, run, replace, Ret() };
    probe.blocks = { entry, cleared, unchanged, join };
    m.funcs.push_back(std::move(probe));
    return m;
}

GirModule ShrinkReplaceAfterClearThroughParameters(bool loop) {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);

    GirFunc probe;
    probe.name = "replace-after-clear-through-parameters";
    probe.scopes = { -1 };
    probe.params = { refTy };
    probe.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    probe.summary.unknown = true;
    GirBlock entry, loopBlock, exit;
    entry.params = { { 0, refTy } };
    GirInst clear;
    clear.op = GirOp::Clear;
    clear.a = 0;
    clear.org = 0;
    entry.insts = { clear };

    if (loop) {
        entry.insts.push_back(Br(1, { 0 }));
        loopBlock.params = { { 1, refTy } };
        auto condition = Def(GirOp::Bool, 2);
        condition.flag = true;
        auto branch = CondBr(2, 2, 1);
        branch.vals = { 1 };
        branch.vals2 = { 1 };
        loopBlock.insts = { condition, branch };
        exit.params = { { 3, refTy } };
    } else {
        auto condition = Def(GirOp::Bool, 1);
        condition.flag = true;
        auto branch = CondBr(1, 1, 1);
        branch.vals = { 0 };
        branch.vals2 = { 0 };
        entry.insts.insert(entry.insts.end(), { condition, branch });
        exit.params = { { 2, refTy } };
    }

    auto ownerParam = loop ? 3 : 2;
    auto value = Int(m, loop ? 4 : 3, "8");
    auto run = Def(GirOp::Arr, loop ? 5 : 4);
    run.ty = ownerTy;
    run.vals = { value.res };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = ownerParam;
    replace.b = run.res;
    replace.org = 0;
    exit.insts = { value, run, replace, Ret() };
    probe.blocks = loop ? vector<GirBlock> { entry, loopBlock, exit }
                        : vector<GirBlock> { entry, exit };
    m.funcs.push_back(std::move(probe));
    return m;
}

GirModule ShrinkReplaceAfterCallArgument() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);

    GirFunc probe;
    probe.name = "replace-after-call-argument";
    probe.params = { refTy };
    probe.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    probe.scopes = { -1 };
    probe.summary.unknown = true;
    GirBlock body;
    body.params = { { 0, refTy } };
    auto clear = Def(GirOp::Clear, -1);
    clear.a = 0;
    clear.org = 0;
    auto call = Def(GirOp::Call, 1);
    call.idx = 2;
    call.vals = { 0 };
    call.org = 0;
    auto run = Def(GirOp::Arr, 2);
    run.ty = ownerTy;
    run.vals = { 1 };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 0;
    replace.b = 2;
    replace.org = 0;
    body.insts = { clear, call, run, replace, Ret() };
    probe.blocks = { body };

    GirFunc reader;
    reader.name = "read-owner";
    reader.params = { refTy };
    reader.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    reader.results = { i64 };
    reader.scopes = { -1 };
    reader.summary.unknown = true;
    GirBlock readerBody;
    readerBody.params = { { 0, refTy } };
    readerBody.insts = { Int(m, 1, "7"), Ret({ 1 }) };
    reader.blocks = { readerBody };

    m.funcs.push_back(std::move(probe));
    m.funcs.push_back(std::move(reader));
    return m;
}

GirModule ShrinkReplaceAfterMixedClearJoin() {
    auto m = Base();
    m.profile = CoreProfile::Shrink;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto ownerTy = m.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = i64 });
    auto refTy = m.RefType(CoreMut::Mut, ownerTy);

    GirFunc probe;
    probe.name = "replace-after-mixed-clear-join";
    probe.params = { refTy, refTy };
    probe.scopes = { -1 };
    probe.roots.params = {
        { 0, { CoreRootRef { CoreRootRef::Param, 0 } } },
        { 1, { CoreRootRef { CoreRootRef::Param, 1 } } },
    };
    probe.summary.unknown = true;

    GirBlock entry, join;
    entry.params = { { 0, refTy }, { 1, refTy } };
    auto condition = Def(GirOp::Bool, 2);
    condition.flag = true;
    GirInst clear;
    clear.op = GirOp::Clear;
    clear.a = 0;
    clear.org = 0;
    auto branch = CondBr(2, 1, 1);
    branch.vals = { 0 };
    branch.vals2 = { 1 };
    entry.insts = { condition, clear, branch };

    join.params = { { 3, refTy } };
    auto value = Int(m, 4, "8");
    auto run = Def(GirOp::Arr, 5);
    run.ty = ownerTy;
    run.vals = { 4 };
    GirInst replace;
    replace.op = GirOp::Replace;
    replace.a = 3;
    replace.b = 5;
    replace.org = 0;
    join.insts = { value, run, replace, Ret() };
    probe.blocks = { entry, join };
    m.funcs.push_back(std::move(probe));
    return m;
}

void AcceptsEmptyOwnerFactsThroughBlockParameters() {
    auto direct = Code(ShrinkReplaceAfterClearThroughParameters(false));
    assert(direct == "");
    auto loop = ShrinkReplaceAfterClearThroughParameters(true);
    auto violation = GirVerifier(loop).Verify();
    if (violation) fprintf(stderr, "%s: %s\n", violation->code.c_str(), violation->message.c_str());
    assert(!violation);
    assert(Code(ShrinkReplaceAfterMixedClearJoin()) == "GIR-V060");
}

void RejectsInvalidShrinkReplacementProofs() {
    auto uncleared = ShrinkReplaceRunThroughPhi();
    auto &entry = Main(uncleared).blocks[0].insts;
    entry.erase(std::remove_if(entry.begin(), entry.end(), [](const GirInst &i) {
        return i.op == GirOp::Clear;
    }), entry.end());
    assert(Code(uncleared) == "GIR-V060");
    assert(Code(ShrinkReplaceClearedOnOneBranch()) == "GIR-V060");
    assert(Code(ShrinkReplaceReceiverViaSlotLoad()) == "");
    assert(Code(ShrinkReplaceFromSavedElement()) == "");
    assert(Code(ShrinkReplaceAfterDiscardedSlotAddress()) == "GIR-V060");
    assert(Code(ShrinkBranchConditionSelectsRun()) == "");
    assert(Code(ShrinkCallResultReadsGlobalBeforeReplace(false)) == "");
    assert(Code(ShrinkCallResultReadsGlobalBeforeReplace(true)) == "");
    for (auto effect : { EmptyOwnerEffect::Load, EmptyOwnerEffect::Snapshot, EmptyOwnerEffect::Length,
                         EmptyOwnerEffect::SliceView, EmptyOwnerEffect::ViewLength,
                         EmptyOwnerEffect::ViewSlice, EmptyOwnerEffect::Index, EmptyOwnerEffect::Push,
                         EmptyOwnerEffect::Pop, EmptyOwnerEffect::PopN, EmptyOwnerEffect::Resize,
                         EmptyOwnerEffect::Store, EmptyOwnerEffect::Append, EmptyOwnerEffect::Replace }) {
        auto code = Code(ShrinkReplaceAfterAliasedEffect(effect));
        assert(code == "GIR-V060");
    }
    for (auto effect : { 0, 1, 2, 3, 4, 5, 6 })
        assert(Code(ShrinkCallSummaryInvalidatesReplace(effect)) == "GIR-V060");
    assert(Code(ShrinkCallSummaryInvalidatesReplace(7)) == "");
    assert(Code(ShrinkLocalReplacementWithUnrelatedParameterRead()) == "");
    for (auto readElement : { false, true })
        assert(Code(ShrinkReplaceAfterClearReadIntoRun(readElement)) == "GIR-V060");
    assert(Code(ShrinkReplaceAfterCallArgument()) == "GIR-V060");
    assert(Code(ShrinkReplaceAfterAppendSourceAlias()) == "GIR-V060");
    assert(Code(ShrinkReplaceAfterSlotInitSourceAlias()) == "GIR-V060");
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

CoreModule CoreWholeArrayAssignment() {
    CoreModule m;
    m.files = { "t.goose" };
    m.profile = CoreProfile::Construction;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::Grow;
    owner.elem = i64;
    auto ownerType = m.Intern(owner);
    auto declaration = CoreOrigin { 0, 1, CoreOriginKind::Let };
    auto assignment = CoreOrigin { 0, 2, CoreOriginKind::Assign };

    CoreImpl impl;
    impl.name = "main";
    impl.vars = { CoreVar { "values", ownerType, CoreVarKind::Var, 0, declaration } };
    impl.body.scope = 0;
    auto initial = make_unique<CoreExpr>();
    initial->kind = CoreExprKind::Arr;
    initial->type = ownerType;
    initial->elems.push_back(CoreInt(i64, "7"));
    CoreStmt let;
    let.kind = CoreStmtKind::Let;
    let.var = 0;
    let.expr = std::move(initial);
    let.org = declaration;
    impl.body.stmts.push_back(std::move(let));
    auto replacement = make_unique<CoreExpr>();
    replacement->kind = CoreExprKind::Arr;
    replacement->type = ownerType;
    replacement->elems.push_back(CoreInt(i64, "11"));
    replacement->elems.push_back(CoreInt(i64, "13"));
    CoreStmt whole;
    whole.kind = CoreStmtKind::AssignWhole;
    whole.place = CoreLocal(0);
    whole.expr = std::move(replacement);
    whole.org = assignment;
    impl.body.stmts.push_back(std::move(whole));

    m.impls.push_back(std::move(impl));
    m.contexts = { CoreContext { .impl = 0 } };
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

    auto constructionSummary = CorePushParamSummary(CoreProfile::Construction);
    constructionSummary.impls[0].summary.rebinds = { CoreTarget { false, 0 } };
    auto constructionSummaryWire = CoreWriter(constructionSummary).Write();
    assert(constructionSummaryWire.find(
               "[\"summary\",[],[],[],[],[[\"t_param\",0]],[],[],[],0,0]") !=
           string::npos);

    auto girConstructionSummary = Base();
    girConstructionSummary.profile = CoreProfile::Construction;
    Main(girConstructionSummary).summary.rebinds = { CoreTarget { false, 0 } };
    auto girConstructionSummaryWire = GirWriter(girConstructionSummary).Write();
    assert(girConstructionSummaryWire.find(
               "[\"summary\",[],[],[],[],[[\"t_param\",0]],[],[],[],0,0]") !=
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

void PilotPushWithoutOriginLowersToValidLowGir() {
    auto m = LetOwnerPush(CoreProfile::Pilot, CoreType::Grow);
    auto &insts = Main(m).blocks[0].insts;
    auto push = find_if(insts.begin(), insts.end(), [](const GirInst &i) { return i.op == GirOp::Push; });
    assert(push != insts.end());
    push->org = -1;
    assert(Code(m) == "");
    auto low = GirToLow(m).Lower();
    assert(Code(low) == "");
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

void LowLimitedOwnerAccessUsesByteCopies() {
    auto high = Base();
    high.profile = CoreProfile::Shrink;
    auto i64 = high.IntType(CoreIntTy::I64);
    auto ownerTy = high.Intern(CoreType { .kind = CoreType::Limited, .elem = i64, .count = 2 });
    auto refOwner = high.RefType(CoreMut::Mut, ownerTy);
    auto viewTy = high.ViewType(CoreMut::Mut, i64);
    auto refI64 = high.RefType(CoreMut::Mut, i64);
    Main(high).slots = { { ownerTy, CoreVarKind::Var, 0, 0 } };
    Main(high).summary.unknown = true;

    auto initial = Int(high, 0, "7");
    auto values = Def(GirOp::Arr, 1);
    values.ty = ownerTy;
    values.vals = { initial.res };
    auto init = Init(0, 1);
    auto owner = Def(GirOp::Slot, 2);
    owner.idx = 0;
    owner.ty = refOwner;
    auto snapshot = Def(GirOp::Snap, 3);
    snapshot.a = owner.res;
    snapshot.snap = GirSnapshotMode::Owner;
    auto zero = Int(high, 4, "0");
    auto element = Def(GirOp::Index, 5);
    element.a = snapshot.res;
    element.b = zero.res;
    element.ty = refI64;
    element.org = 0;
    auto firstLoad = Def(GirOp::Load, 6);
    firstLoad.a = element.res;
    auto replacement = Int(high, 7, "9");
    GirInst store;
    store.op = GirOp::Store;
    store.a = element.res;
    store.b = replacement.res;
    store.org = 0;
    auto secondLoad = Def(GirOp::Load, 8);
    secondLoad.a = element.res;
    auto print = Def(GirOp::Print, -1);
    print.parts = { { false, "", firstLoad.res }, { false, " ", secondLoad.res } };
    print.org = 0;
    Main(high).blocks[0].insts = { Enter(0), initial, values, init, owner, snapshot, zero,
                                   element, firstLoad, replacement, store, secondLoad, print,
                                   Leave(0), Ret() };

    assert(Code(high) == "");
    auto low = GirToLow(high).Lower();
    assert(!GirVerifier(low).Verify());
    for (auto &block : low.funcs[0].blocks)
        for (auto &inst : block.insts)
            assert(inst.op != GirOp::PLoad && inst.op != GirOp::PStore);
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

GirModule ByteConstructionModule() {
    auto m = Base();
    m.profile = CoreProfile::Construction;
    auto u8 = m.IntType(CoreIntTy::U8);
    CoreType owner;
    owner.kind = CoreType::Grow;
    owner.elem = u8;
    auto ownerType = m.Intern(owner);
    Main(m).slots = { { ownerType, CoreVarKind::Let, 0, 0 } };

    auto count = Int(m, 0, "3");
    GirInst open = Def(GirOp::DestOpen, 1);
    open.destReceiver = GirDestSlotReceiver { 0 };
    open.ty = ownerType;
    open.request = CoreRequest::Value;
    open.knownCount = 0;
    open.org = 0;
    GirInst write;
    write.op = GirOp::DestBytes;
    write.org = 0;
    write.a = 1;
    write.bytes = { 65, 0, 66 };
    write.org = 0;
    auto interveningValue = Int(m, 2, "1");
    GirInst finish = Def(GirOp::DestFinish, 3);
    finish.a = 1;
    GirInst publish;
    publish.op = GirOp::DestPublish;
    publish.org = 0;
    publish.a = 3;
    Main(m).blocks[0].insts = { Enter(0), count, open, interveningValue, write, finish, publish, Leave(0), Ret() };
    return m;
}

GirModule GrowArrayConstructionModule() {
    auto m = Base();
    m.profile = CoreProfile::Construction;
    auto i64 = m.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::Grow;
    owner.elem = i64;
    auto ownerType = m.Intern(owner);
    Main(m).slots = { { ownerType, CoreVarKind::Let, 0, 0 } };

    auto count = Int(m, 0, "3");
    auto first = Int(m, 1, "7");
    auto second = Int(m, 2, "11");
    auto third = Int(m, 3, "13");
    GirInst open = Def(GirOp::DestOpen, 4);
    open.destReceiver = GirDestSlotReceiver { 0 };
    open.ty = ownerType;
    open.request = CoreRequest::Value;
    open.knownCount = 0;
    open.org = 0;
    auto write = [](int value) {
        GirInst i;
        i.op = GirOp::DestWrite;
        i.a = 4;
        i.b = value;
        i.org = 0;
        return i;
    };
    GirInst finish = Def(GirOp::DestFinish, 5);
    finish.a = 4;
    finish.org = 0;
    GirInst publish;
    publish.op = GirOp::DestPublish;
    publish.org = 0;
    publish.a = 5;
    publish.org = 0;
    Main(m).blocks[0].insts = {
        Enter(0), count, first, second, third, open, write(1), write(2), write(3),
        finish, publish, Leave(0), Ret(),
    };
    return m;
}

void ConstructionBytesUseLinearDestinationProtocol() {
    auto high = ByteConstructionModule();
    assert(Code(high) == "");
    assert(!GirVerifier(high).Verify());
    auto encoded = GirWriter(high).Write();
    assert(encoded.find("[\"dest\",") != string::npos);
    assert(encoded.find("[\"built\",") != string::npos);

    auto low = GirToLow(high).Lower();
    assert(!GirVerifier(low).Verify());
    assert(low.profile == CoreProfile::Construction);
    assert(low.pointerBytes == sizeof(void *));
    assert(low.lowtargets.empty());
    auto writes = 0;
    auto bumps = 0;
    auto headerInitializations = 0;
    auto lengthUpdates = 0;
    for (auto &func : low.funcs) for (auto &block : func.blocks) for (auto &inst : block.insts) {
        writes += inst.op == GirOp::Event && inst.event == GirEventKind::Write;
        bumps += inst.op == GirOp::StackBump;
        headerInitializations += inst.op == GirOp::HdrInit;
        lengthUpdates += inst.op == GirOp::HdrSetLen;
        assert(inst.op != GirOp::DestOpen && inst.op != GirOp::DestBytes &&
               inst.op != GirOp::DestFinish && inst.op != GirOp::DestPublish);
    }
    assert(writes == 3);
    assert(bumps == 3);
    assert(headerInitializations == 1);
    assert(lengthUpdates == 1);
}

void ConstructionBytesRejectIncompleteOrMismatchedDestinations() {
    auto missingPublish = ByteConstructionModule();
    Main(missingPublish).blocks[0].insts.erase(Main(missingPublish).blocks[0].insts.begin() + 6);
    assert(Code(missingPublish) == "GIR-V060");

    auto wrongCount = ByteConstructionModule();
    Main(wrongCount).blocks[0].insts[1].text = "2";
    assert(Code(wrongCount) == "GIR-V060");
}

void ConstructionGrowArrayUsesElementDestinations() {
    auto high = GrowArrayConstructionModule();
    assert(Code(high) == "");
    assert(!GirVerifier(high).Verify());
    auto encoded = GirWriter(high).Write();
    assert(encoded.find("[\"x_dest_write\",4,1,[0]]") != string::npos);

    auto low = GirToLow(high).Lower();
    assert(!GirVerifier(low).Verify());
    auto copies = 0;
    auto bumps = 0;
    auto headerInitializations = 0;
    auto lengthUpdates = 0;
    for (auto &func : low.funcs) for (auto &block : func.blocks) for (auto &inst : block.insts) {
        copies += inst.op == GirOp::BytesCopy;
        bumps += inst.op == GirOp::StackBump;
        headerInitializations += inst.op == GirOp::HdrInit;
        lengthUpdates += inst.op == GirOp::HdrSetLen;
        assert(inst.op != GirOp::DestOpen && inst.op != GirOp::DestWrite &&
               inst.op != GirOp::DestFinish && inst.op != GirOp::DestPublish);
    }
    assert(copies == 3);
    assert(bumps == 3);
    assert(headerInitializations == 1);
    assert(lengthUpdates == 1);
}

void ConstructionWholeAssignmentUsesOwnerDestination() {
    auto core = CoreWholeArrayAssignment();
    CoreSummarizer(core).Run();
    auto numbering = [&] { CoreWriter writer(core); writer.Write(); return writer; }();
    auto high = GirLowerer(core, numbering.FileTable(), numbering.OriginTable(),
                           [&](const CoreOrigin &origin) { return numbering.OriginId(origin); }).Lower();
    high.diagfiles = numbering.DiagFileTable();
    high.filemodules = numbering.FileModuleTable();
    assert(!GirVerifier(high).Verify());
    auto encoded = GirWriter(high).Write();
    assert(encoded.find("[\"dr_whole\",") != string::npos);

    int clearIndex = -1;
    int wholeOpenIndex = -1;
    for (size_t block = 0; block < high.funcs[0].blocks.size(); block++)
        for (size_t index = 0; index < high.funcs[0].blocks[block].insts.size(); index++) {
            auto &inst = high.funcs[0].blocks[block].insts[index];
            if (inst.op == GirOp::Clear) clearIndex = (int)index;
            if (inst.op == GirOp::DestOpen && holds_alternative<GirDestWholeReceiver>(inst.destReceiver))
                wholeOpenIndex = (int)index;
        }
    assert(clearIndex >= 0 && wholeOpenIndex > clearIndex);

    auto low = GirToLow(high).Lower();
    assert(!GirVerifier(low).Verify());
}

void ConstructionRejectsDetachedGrowArrayAggregates() {
    auto m = GrowArrayConstructionModule();
    auto first = Int(m, 0, "7");
    auto detached = Def(GirOp::Arr, 1);
    detached.ty = Main(m).slots[0].ty;
    detached.vals = { 0 };
    auto init = Init(0, 1);
    Main(m).blocks[0].insts = { Enter(0), first, detached, init, Leave(0), Ret() };
    assert(Code(m) == "GIR-V060");
}

void ConstructionTargetsRejectEmptyAndRepeatedMemberSets() {
    auto empty = Base();
    empty.profile = CoreProfile::Construction;
    empty.targets = { CoreTargetSet {} };
    assert(Code(empty) == "GIR-V001");

    auto repeated = Base();
    repeated.profile = CoreProfile::Construction;
    repeated.targets = { CoreTargetSet { { 0, 0 } } };
    assert(Code(repeated) == "GIR-V001");
}

GirModule LowConstructionObservationModule() {
    auto m = LowBase();
    m.profile = CoreProfile::Construction;
    auto bytes = Def(GirOp::StaticBytes, 1);
    bytes.bytes = { 65, 0, 255, 66 };
    auto destination = Def(GirOp::TraceId, 2);
    destination.trace = GirTraceKind::Destination;
    GirInst begin;
    begin.op = GirOp::Event;
    begin.vals = { 2 };
    GirInst output;
    output.op = GirOp::OutBytes;
    output.a = 1;
    output.b = 3;
    output.org = 0;
    GirInst publish = begin;
    publish.event = GirEventKind::Publish;
    Main(m).blocks[0].insts = { bytes, destination, begin, Int(m, 3, "4"), output, publish, Ret() };
    return m;
}

void ConstructionLowOperationsRetainExactByteAndEventWire() {
    auto m = LowConstructionObservationModule();
    assert(Code(m) == "");
    auto wire = GirWriter(m).WriteLow();
    assert(wire.find("[\"l_static\",1,[65,0,255,66]]") != string::npos);
    assert(wire.find("[\"l_trace_id\",2,\"destination\"]") != string::npos);
    assert(wire.find("[\"l_event\",\"begin\",[2],\"\"]") != string::npos);
    assert(wire.find("[\"l_out_bytes\",1,3,[0]]") != string::npos);

    Main(m).blocks[0].insts[2].reason = GirEventReason::Repeat;
    assert(Code(m) == "GIR-V010");
    m = LowConstructionObservationModule();
    Main(m).blocks[0].insts[2].event = GirEventKind::Write;
    assert(Code(m) == "GIR-V010");
    m = LowConstructionObservationModule();
    Main(m).blocks[0].insts[1].trace = (GirTraceKind)2;
    assert(Code(m) == "GIR-V010");
    m = LowConstructionObservationModule();
    Main(m).blocks[0].insts[3].text = "5";
    assert(Code(m) == "GIR-V090");
    m = LowConstructionObservationModule();
    Main(m).blocks[0].insts[3].text = "-1";
    assert(Code(m) == "GIR-V090");
}

void ConstructionLowFormattingChecksScalarKind() {
    auto m = LowConstructionObservationModule();
    GirMember bytes;
    bytes.kind = GirMember::Bytes;
    bytes.size = 32;
    Main(m).members = { bytes };
    auto pointer = Def(GirOp::FrameAddr, 1);
    pointer.idx = 0;
    auto format = Def(GirOp::Format, 3);
    format.a = 2;
    format.b = 1;
    Main(m).blocks[0].insts = { pointer, Int(m, 2, "-17"), format, Ret() };
    assert(Code(m) == "");
    Main(m).blocks[0].insts[2].format = GirFormatKind::Uint;
    assert(Code(m) == "GIR-V010");
    Main(m).blocks[0].insts[2].format = GirFormatKind::Bool;
    assert(Code(m) == "GIR-V010");
    Main(m).blocks[0].insts[2].format = GirFormatKind::Int;
    Main(m).members[0].size = 31;
    assert(Code(m) == "GIR-V090");
}

void ConstructionCarrierOwnershipCrossesBranchParameters() {
    auto m = ByteConstructionModule();
    assert(Code(m) == "");
    auto destination = Main(m).blocks[0].insts[2];
    auto type = m.CarrierType(CoreType::Dest, destination.ty, CoreRequest::Value);
    auto built = m.CarrierType(CoreType::Built, destination.ty, CoreRequest::Value);
    auto &entry = Main(m).blocks[0];
    entry.insts = { Enter(0), Int(m, 0, "3"), destination, Br(1, { 1 }) };
    GirInst write;
    write.op = GirOp::DestBytes;
    write.org = 0;
    write.a = 2;
    write.bytes = { 65, 0, 66 };
    write.org = 0;
    auto finish = Def(GirOp::DestFinish, 3);
    finish.a = 2;
    GirBlock body;
    body.params = { { 2, type } };
    body.insts = { write, finish, Br(2, { 3 }) };
    GirInst publish;
    publish.op = GirOp::DestPublish;
    publish.org = 0;
    publish.a = 4;
    GirBlock exit;
    exit.params = { { 4, built } };
    exit.insts = { publish, Leave(0), Ret() };
    Main(m).blocks.push_back(body);
    Main(m).blocks.push_back(exit);
    assert(Code(m) == "");

    Main(m).blocks[2].insts.insert(Main(m).blocks[2].insts.begin() + 1, publish);
    assert(Code(m) == "GIR-V060");
}

void ConstructionAbandonmentProducesOneCancellationCertificate() {
    auto m = ByteConstructionModule();
    auto &insts = Main(m).blocks[0].insts;
    auto abandon = Def(GirOp::DestAbandon, 3);
    abandon.a = 1;
    abandon.org = 0;
    GirInst cancel;
    cancel.op = GirOp::DestCancel;
    cancel.a = 3;
    cancel.org = 0;
    insts[5] = abandon;
    insts[6] = cancel;
    assert(Code(m) == "");
    auto wire = GirWriter(m).Write();
    assert(wire.find("[\"cancelled\",") != string::npos);
    assert(wire.find("[\"i_dest_abandon\",3,1,[0]]") != string::npos);
    insts.erase(insts.begin() + 6);
    assert(Code(m) == "GIR-V060");
}

GirModule ConstructionCallModule() {
    auto m = GrowArrayConstructionModule();
    auto type = Main(m).slots[0].ty;
    auto destinationType = m.CarrierType(CoreType::Dest, type, CoreRequest::Value);
    GirFunc make;
    make.name = "make";
    make.results = { type };
    make.roots.results = { {} };
    make.resultProtocols = { { CoreRequest::Value, nullopt } };
    make.scopes = { -1 };
    make.summary.constructs = { 0 };
    auto write = GirInst {};
    write.op = GirOp::DestWrite;
    write.org = 0;
    write.a = 0;
    write.b = 1;
    auto finish = Def(GirOp::DestFinish, 2);
    finish.a = 0;
    make.blocks = { GirBlock { { { 0, destinationType } },
                              { Enter(0), Int(m, 1, "7"), write, finish, Leave(0), Ret({ 2 }) } } };
    m.funcs.push_back(make);
    auto open = Main(m).blocks[0].insts[5];
    open.res = 1;
    auto call = Def(GirOp::CallConstruct, 2);
    call.idx = 1;
    call.vals2 = { 1 };
    call.org = 0;
    auto publish = GirInst {};
    publish.op = GirOp::DestPublish;
    publish.org = 0;
    publish.a = 2;
    Main(m).blocks[0].insts = { Enter(0), Int(m, 0, "1"), open, call, publish, Leave(0), Ret() };
    return m;
}

void ConstructionCallsReturnTheTransferredChannel() {
    auto m = ConstructionCallModule();
    assert(Code(m) == "");
    auto wire = GirWriter(m).Write();
    assert(wire.find("[\"i_call_construct\",2,1,[],[1],[0]]") != string::npos);
    assert(wire.find("\"value\",[]]") != string::npos);
    Main(m).blocks[0].insts.insert(Main(m).blocks[0].insts.begin() + 4, Main(m).blocks[0].insts[4]);
    assert(Code(m) == "GIR-V060");
    m = ConstructionCallModule();
    m.funcs[1].summary.constructs.clear();
    assert(Code(m) == "GIR-V050");
    m = ConstructionCallModule();
    m.funcs[1].resultProtocols[0].request = CoreRequest::ElementRun;
    assert(Code(m) == "GIR-V010");
}

GirModule ConstructionFixedTargetModule() {
    auto m = Base();
    m.profile = CoreProfile::Construction;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto call = Def(GirOp::Call, 0);
    call.idx = 1;
    call.org = 0;
    Main(m).blocks[0].insts = { call, Ret() };
    GirFunc target;
    target.name = "target";
    target.results = { i64 };
    target.roots.results = { {} };
    target.resultProtocols = { {} };
    target.scopes = { -1 };
    GirInst invoke;
    invoke.op = GirOp::Invoke;
    invoke.idx = 2;
    invoke.a = 1;
    invoke.escapes = { { 0, 2, {} } };
    invoke.org = 0;
    target.blocks = { GirBlock { {}, { invoke } }, GirBlock { {}, { Int(m, 0, "0"), Ret({ 0 }) } },
                      GirBlock { { { 1, i64 } }, { Ret({ 1 }) } } };
    GirFunc helper;
    helper.name = "helper";
    helper.scopes = { -1 };
    helper.summary.needs = { 0 };
    helper.summary.escapes = { 0 };
    GirInst escape;
    escape.op = GirOp::Escape;
    escape.idx = 0;
    escape.vals = { 0 };
    escape.org = 0;
    helper.blocks = { GirBlock { {}, { Int(m, 0, "7"), escape } } };
    m.funcs.push_back(target);
    m.funcs.push_back(helper);
    m.targets = { CoreTargetSet { { 1 } } };
    return m;
}

void ConstructionTargetEdgesAreTypedAndDerivedFromBodies() {
    auto m = ConstructionFixedTargetModule();
    assert(Code(m) == "");
    auto wire = GirWriter(m).Write();
    assert(wire.find("[\"t_invoke\",2,[],[],1,[],[[\"escape_edge\",0,2,[]]],[0]]") != string::npos);
    m.funcs[2].summary.escapes.clear();
    assert(Code(m) == "GIR-V050");
    m = ConstructionFixedTargetModule();
    m.funcs[1].blocks[0].insts[0].escapes.clear();
    assert(Code(m) == "GIR-V020");
    m = ConstructionFixedTargetModule();
    m.funcs[1].blocks[2].params[0].second = m.BoolType();
    assert(Code(m) == "GIR-V010");
    m = ConstructionFixedTargetModule();
    m.targets[0].members = { 0 };
    assert(Code(m) == "GIR-V010");
}

GirModule ConstructionVariableTargetModule() {
    auto m = ConstructionCallModule();
    auto type = m.funcs[1].results[0];
    auto dest = m.CarrierType(CoreType::Dest, type, CoreRequest::Value);
    auto built = m.CarrierType(CoreType::Built, type, CoreRequest::Value);
    auto cancelled = m.CarrierType(CoreType::Cancelled, type, CoreRequest::Value);
    GirInst invoke;
    invoke.op = GirOp::Invoke;
    invoke.idx = 2;
    invoke.vals2 = { 0 };
    invoke.a = 1;
    invoke.escapes = { { 0, 2, {} } };
    invoke.org = 0;
    GirInst cancel;
    cancel.op = GirOp::DestCancel;
    cancel.a = 3;
    cancel.org = 0;
    auto land = Def(GirOp::DestRelocate, 4);
    land.a = 2;
    land.reason = GirEventReason::ExitValue;
    land.org = 0;
    m.funcs[1].blocks = { GirBlock { { { 0, dest } }, { invoke } },
                          GirBlock { { { 1, built } }, { Ret({ 1 }) } },
                          GirBlock { { { 2, built }, { 3, cancelled } }, { cancel, land, Ret({ 4 }) } } };
    GirFunc helper;
    helper.name = "helper";
    helper.results = { type };
    helper.roots.results = { {} };
    helper.resultProtocols = { { CoreRequest::Value, nullopt } };
    helper.scopes = { -1 };
    helper.summary.needs = { 0 };
    helper.summary.escapes = { 0 };
    auto target = Def(GirOp::TargetDest, 1);
    target.idx = 0;
    target.idx2 = 0;
    target.ty = type;
    target.request = CoreRequest::Value;
    target.org = 0;
    GirInst write;
    write.op = GirOp::DestWrite;
    write.org = 0;
    write.a = 1;
    write.b = 2;
    auto finish = Def(GirOp::DestFinish, 3);
    finish.a = 1;
    auto abandon = Def(GirOp::DestAbandon, 4);
    abandon.a = 0;
    abandon.org = 0;
    GirInst escape;
    escape.op = GirOp::Escape;
    escape.idx = 0;
    escape.vals = { 3 };
    escape.vals2 = { 4 };
    escape.org = 0;
    helper.blocks = { GirBlock { { { 0, dest } }, { target, Int(m, 2, "7"), write, finish, abandon, escape } } };
    m.funcs.push_back(helper);
    m.targets = { CoreTargetSet { { 1 } } };
    return m;
}

void ConstructionVariableExitRequiresCancellationBeforeLanding() {
    auto m = ConstructionVariableTargetModule();
    assert(Code(m) == "");
    auto &catchBody = m.funcs[1].blocks[2].insts;
    swap(catchBody[0], catchBody[1]);
    assert(Code(m) == "GIR-V060");
    m = ConstructionVariableTargetModule();
    m.funcs[2].blocks[0].insts.back().vals2.clear();
    assert(Code(m) == "GIR-V010");
    m = ConstructionVariableTargetModule();
    m.funcs[1].blocks[2].insts[1].reason = GirEventReason::HeaderRemoval;
    assert(Code(m) == "GIR-V010");
}

GirModule ConstructionFixedMultiResultModule() {
    auto m = Base();
    m.profile = CoreProfile::Construction;
    auto i64 = m.IntType(CoreIntTy::I64);
    auto boolean = m.BoolType();
    GirFunc pair;
    pair.name = "pair";
    pair.params = { i64 };
    pair.results = { i64, boolean };
    pair.roots.results = { {}, {} };
    pair.resultProtocols = { {}, {} };
    pair.scopes = { -1 };
    auto yes = Def(GirOp::Bool, 1);
    yes.flag = true;
    pair.blocks = { GirBlock { { { 0, i64 } }, { yes, Ret({ 0, 1 }) } } };
    m.funcs.push_back(pair);
    auto call = Def(GirOp::Call, 1);
    call.idx = 1;
    call.vals = { 0 };
    call.org = 0;
    auto first = Def(GirOp::Result, 2);
    first.a = 1;
    first.idx = 0;
    auto second = Def(GirOp::Result, 3);
    second.a = 1;
    second.idx = 1;
    GirInst print;
    print.op = GirOp::Print;
    print.parts = { { false, "", 2 }, { true, " ", 0 }, { false, "", 3 } };
    print.org = 0;
    Main(m).summary.outputs = true;
    Main(m).blocks[0].insts = { Int(m, 0, "7"), call, first, second, print, Ret() };
    return m;
}

void ConstructionFixedResultsUseExplicitOutputChannels() {
    auto m = ConstructionFixedMultiResultModule();
    assert(Code(m) == "");
    auto low = GirToLow(m).Lower();
    assert(Code(low) == "");
    assert(low.funcs[1].params.size() == 4);
    for (auto &function : low.funcs) {
        assert(function.results.empty());
        for (auto &block : function.blocks) for (auto &inst : block.insts)
            if (inst.op == GirOp::Ret) assert(inst.vals.empty());
    }
}

}  // namespace

GirModule ConstructionRecursiveArrayModule() {
    auto m = Base();
    m.profile = CoreProfile::Construction;
    auto byte = m.IntType(CoreIntTy::U8);
    CoreType variable;
    variable.kind = CoreType::VarArr;
    variable.elem = byte;
    auto inner = m.Intern(variable);
    CoreType fixed;
    fixed.kind = CoreType::Arr;
    fixed.elem = inner;
    fixed.count = 2;
    auto outer = m.Intern(fixed);
    Main(m).slots = { { outer, CoreVarKind::Let, 0, 0 } };
    GirInst open = Def(GirOp::DestOpen, 0);
    open.destReceiver = GirDestSlotReceiver { 0 };
    open.ty = outer;
    open.org = 0;
    auto child = [&](int result, int parent) {
        auto instruction = Def(GirOp::DestChild, result);
        instruction.a = parent;
        instruction.ty = inner;
        instruction.org = 0;
        return instruction;
    };
    auto bytes = [&](int destination, vector<uint8_t> values) {
        GirInst instruction;
        instruction.op = GirOp::DestBytes;
        instruction.a = destination;
        instruction.bytes = std::move(values);
        instruction.org = 0;
        return instruction;
    };
    auto finish = [&](int result, int destination) {
        auto instruction = Def(GirOp::DestFinish, result);
        instruction.a = destination;
        instruction.org = 0;
        return instruction;
    };
    auto attach = [&](int completion) {
        GirInst instruction;
        instruction.op = GirOp::DestAttach;
        instruction.a = 0;
        instruction.b = completion;
        instruction.org = 0;
        return instruction;
    };
    GirInst publish;
    publish.op = GirOp::DestPublish;
    publish.org = 0;
    publish.a = 5;
    publish.org = 0;
    auto slot = Def(GirOp::Slot, 6);
    slot.idx = 0;
    auto snapshot = Def(GirOp::Snap, 7);
    snapshot.a = 6;
    auto index = Def(GirOp::Index, 9);
    index.a = 7;
    index.b = 8;
    index.org = 0;
    auto innerSnapshot = Def(GirOp::Snap, 10);
    innerSnapshot.a = 9;
    auto render = Def(GirOp::Render, 11);
    render.a = 10;
    render.org = 0;
    GirInst print;
    print.op = GirOp::Print;
    print.parts = { { false, "", 11 } };
    print.org = 0;
    Main(m).summary.outputs = true;
    Main(m).summary.aborts = true;
    Main(m).blocks[0].insts = {
        Enter(0), open, child(1, 0), bytes(1, { 65, 0 }), finish(2, 1), attach(2),
        child(3, 0), bytes(3, { 255 }), finish(4, 3), attach(4), finish(5, 0), publish,
        slot, snapshot, Int(m, 8, "0"), index, innerSnapshot, render, print, Leave(0), Ret(),
    };
    return m;
}

void ConstructionRecursiveArraysUseExplicitPackedTraversal() {
    auto m = ConstructionRecursiveArrayModule();
    assert(Code(m) == "");
    auto low = GirToLow(m).Lower();
    assert(Code(low) == "");
    assert(low.funcs[0].blocks.size() > 4);
    assert(any_of(low.funcs[0].members.begin(), low.funcs[0].members.end(), [](auto &member) {
        return member.kind == GirMember::Dynamic;
    }));
    for (auto &type : low.types)
        assert(type.kind == CoreType::Int || type.kind == CoreType::Bool || type.kind == CoreType::Ptr || type.kind == CoreType::Unit);
    auto wire = GirWriter(m).Write();
    assert(wire.find("\"i_render\"") != string::npos);
    auto escaped = m;
    auto store = GirInst {};
    store.op = GirOp::Init;
    store.idx = 1;
    store.a = 11;
    store.org = 0;
    Main(escaped).slots.push_back({ escaped.SliceType(CoreMut::Const, escaped.IntType(CoreIntTy::U8)), CoreVarKind::Let, 0, 1 });
    Main(escaped).blocks[0].insts.insert(Main(escaped).blocks[0].insts.end() - 2, store);
    assert(Code(escaped) != "");
    auto incomplete = m;
    auto fixed = incomplete.Type(Main(incomplete).slots[0].ty);
    fixed.count = 3;
    auto lengthThree = incomplete.Intern(fixed);
    Main(incomplete).slots[0].ty = lengthThree;
    Main(incomplete).blocks[0].insts[1].ty = lengthThree;
    assert(Code(incomplete) == "GIR-V060");
    for (bool dynamicProducer : { false, true }) {
        auto invalid = m;
        auto producer = invalid.Type(Main(invalid).slots[0].ty);
        if (dynamicProducer) producer.kind = CoreType::Grow;
        else producer.count = 3;
        auto adapt = Def(GirOp::DestAdapt, 1);
        adapt.a = 0;
        adapt.ty = invalid.Intern(producer);
        adapt.org = 0;
        GirInst trap;
        trap.op = GirOp::Abort;
        trap.abort = GirAbortKind::Assert;
        trap.org = 0;
        Main(invalid).blocks[0].insts = { Enter(0), Main(invalid).blocks[0].insts[1], adapt, trap };
        assert(Code(invalid) == "GIR-V010");
    }
}

void ConstructionCallsAndCarrierBranchesLowerToPrimitiveChannels() {
    auto calls = ConstructionCallModule();
    assert(Code(GirToLow(calls).Lower()) == "");
    auto m = ByteConstructionModule();
    auto destination = Main(m).blocks[0].insts[2];
    auto type = m.CarrierType(CoreType::Dest, destination.ty, CoreRequest::Value);
    auto built = m.CarrierType(CoreType::Built, destination.ty, CoreRequest::Value);
    Main(m).blocks[0].insts = { Enter(0), Int(m, 0, "3"), destination, Br(1, { 1 }) };
    GirInst write;
    write.op = GirOp::DestBytes;
    write.org = 0;
    write.a = 2;
    write.bytes = { 65, 0, 66 };
    write.org = 0;
    auto finish = Def(GirOp::DestFinish, 3);
    finish.a = 2;
    GirInst publish;
    publish.op = GirOp::DestPublish;
    publish.org = 0;
    publish.a = 4;
    Main(m).blocks.push_back({ { { 2, type } }, { write, finish, Br(2, { 3 }) } });
    Main(m).blocks.push_back({ { { 4, built } }, { publish, Leave(0), Ret() } });
    assert(Code(m) == "");
    assert(Code(GirToLow(m).Lower()) == "");
}

GirModule ConstructionAliasedProvenanceModule() {
    auto m = LowBase();
    m.profile = CoreProfile::Construction;
    auto integer = m.IntType(CoreIntTy::I64);
    auto pointer = m.PtrType();
    auto bytes = Def(GirOp::StaticBytes, 1);
    bytes.bytes = { 65 };
    auto scope = Def(GirOp::SourceEnter, 2);
    auto storage0 = Def(GirOp::TraceId, 3);
    storage0.trace = GirTraceKind::Storage;
    auto source0 = Def(GirOp::SourceNew, 4);
    source0.a = 3;
    auto storage1 = Def(GirOp::TraceId, 5);
    storage1.trace = GirTraceKind::Storage;
    auto source1 = Def(GirOp::SourceNew, 6);
    source1.a = 5;
    auto destination = Def(GirOp::TraceId, 7);
    destination.trace = GirTraceKind::Destination;
    GirInst begin;
    begin.op = GirOp::Event;
    begin.vals = { 7 };
    auto shadow = Def(GirOp::SourceCallPush, 8);
    shadow.vals = { 4, 6, -1 };
    GirInst call;
    call.op = GirOp::Call;
    call.idx = 1;
    call.vals = { 0, 1, 1, 7 };
    call.org = 0;
    GirInst pop;
    pop.op = GirOp::SourceCallPop;
    pop.a = 8;
    GirInst leave;
    leave.op = GirOp::SourceLeave;
    leave.a = 2;
    Main(m).blocks[0].insts = { bytes, scope, storage0, source0, storage1, source1, destination, begin, shadow, call, pop, leave, Ret() };
    GirFunc callee;
    callee.name = "copy_aliases";
    callee.params = { integer, pointer, pointer, integer };
    callee.scopes = { -1 };
    auto inner = Def(GirOp::SourceEnter, 4);
    auto first = Def(GirOp::SourceParam, 5);
    first.idx = 1;
    auto second = Def(GirOp::SourceParam, 6);
    second.idx = 2;
    GirInst copyFirst;
    copyFirst.op = GirOp::SourceCopy;
    copyFirst.a = 5;
    copyFirst.b = 3;
    auto copySecond = copyFirst;
    copySecond.a = 6;
    auto innerLeave = leave;
    innerLeave.a = 4;
    callee.blocks = { { { { 0, integer }, { 1, pointer }, { 2, pointer }, { 3, integer } },
                       { inner, first, second, copyFirst, copySecond, innerLeave, Ret() } } };
    m.funcs.push_back(std::move(callee));
    return m;
}

void ConstructionProvenanceShadowsDistinguishAliasedArguments() {
    auto m = ConstructionAliasedProvenanceModule();
    assert(Code(m) == "");
    auto wire = GirWriter(m).WriteLow();
    assert(wire.find("[\"l_source_call_push\",8,[[4],[6],[]]]") != string::npos);
    auto missing = m;
    Main(missing).blocks[0].insts[8].vals[1] = -1;
    assert(Code(missing) == "GIR-V090");
    auto wrongStorage = m;
    Main(wrongStorage).blocks[0].insts[2].trace = GirTraceKind::Destination;
    assert(Code(wrongStorage) == "GIR-V090");
    auto wrongParameter = m;
    wrongParameter.funcs[1].blocks[0].insts[1].idx = 3;
    assert(Code(wrongParameter) == "GIR-V090");
    auto unclosedCall = m;
    Main(unclosedCall).blocks[0].insts.erase(Main(unclosedCall).blocks[0].insts.begin() + 10);
    assert(Code(unclosedCall) == "GIR-V090");
    auto programPointer = m;
    Main(programPointer).blocks[0].insts[8].vals[0] = 1;
    assert(Code(programPointer) == "GIR-V090");
    auto deadSource = m;
    auto &instructions = deadSource.funcs[1].blocks[0].insts;
    swap(instructions[4], instructions[5]);
    assert(Code(deadSource) == "GIR-V090");
}

GirModule ConstructionReturnedReferenceCopyModule() {
    auto m = ByteConstructionModule();
    auto grow = Main(m).slots[0].ty;
    auto integer = m.IntType(CoreIntTy::I64);
    auto reference = m.RefType(CoreMut::Mut, grow);
    Main(m).slots = { { integer, CoreVarKind::Let, 0, 0 }, { grow, CoreVarKind::Let, 0, 1 }, { grow, CoreVarKind::Let, 0, 2 } };
    auto &instructions = Main(m).blocks[0].insts;
    get<GirDestSlotReceiver>(instructions[2].destReceiver).slot = 1;
    instructions.insert(instructions.begin() + 2, Init(0, 0));
    instructions.resize(instructions.size() - 2);
    auto slot = Def(GirOp::Slot, 4);
    slot.idx = 1;
    auto open = Def(GirOp::DestOpen, 5);
    open.ty = grow;
    open.destReceiver = GirDestSlotReceiver { 2 };
    open.org = 0;
    auto call = Def(GirOp::Call, 6);
    call.idx = 1;
    call.vals = { 4 };
    call.org = 0;
    GirInst copy;
    copy.op = GirOp::DestCopy;
    copy.a = 5;
    copy.b = 6;
    copy.org = 0;
    auto finish = Def(GirOp::DestFinish, 7);
    finish.a = 5;
    GirInst publish;
    publish.op = GirOp::DestPublish;
    publish.a = 7;
    publish.org = 0;
    for (auto &instruction : vector<GirInst> { slot, open, call, copy, finish, publish, Leave(0), Ret() }) instructions.push_back(instruction);
    GirFunc identity;
    identity.name = "identity";
    identity.params = { reference };
    identity.results = { reference };
    identity.resultProtocols = { {} };
    identity.slots = { { reference, CoreVarKind::Let, 0, 0 } };
    identity.scopes = { -1 };
    identity.roots.params = { { 0, { CoreRootRef { CoreRootRef::Param, 0 } } } };
    identity.roots.results = { { CoreRootRef { CoreRootRef::Param, 0 } } };
    identity.blocks = { { { { 0, reference } }, { Enter(0), Init(0, 0), Leave(0), Ret({ 0 }) } } };
    m.funcs.push_back(std::move(identity));
    return m;
}

void ConstructionReturnedReferenceRetainsCopyProvenance() {
    auto m = ConstructionReturnedReferenceCopyModule();
    assert(Code(m) == "");
    auto low = GirToLow(m).Lower();
    assert(Code(low) == "");
    auto wire = GirWriter(low).WriteLow();
    assert(wire.find("\"l_source_result\"") != string::npos);
    assert(wire.find("\"l_source_call_get\"") != string::npos);
    assert(wire.find("\"l_source_copy\"") != string::npos);
}

void StorageSummaryCoverageNormalizesSpecializedAndGenericRoots() {
    for (auto specialized : { false, true }) {
        auto m = Base();
        m.profile = CoreProfile::Shrink;
        auto integer = m.IntType(CoreIntTy::I64);
        CoreType owner;
        owner.kind = CoreType::Grow;
        owner.elem = integer;
        auto grow = m.Intern(owner);
        auto reference = m.RefType(CoreMut::Mut, grow);
        GirGlobal global;
        global.name = "owner";
        global.ty = grow;
        global.kind = CoreVarKind::Var;
        global.org = 0;
        global.init.name = "owner";
        global.init.results = { grow };
        global.init.roots.results = { {} };
        global.init.summary.unknown = true;
        auto array = Def(GirOp::Arr, 0);
        array.ty = grow;
        global.init.blocks = { { {}, { array, Ret({ 0 }) } } };
        m.globals.push_back(std::move(global));
        GirFunc touch;
        touch.name = "touch";
        touch.params = { reference };
        touch.scopes = { -1 };
        touch.roots.params = { { 0, { CoreRootRef { specialized ? CoreRootRef::Global : CoreRootRef::Param, 0 } } } };
        for (auto *targets : { &touch.summary.reads, &touch.summary.writes, &touch.summary.grows, &touch.summary.shrinks })
            targets->push_back({ false, 0 });
        touch.summary.aborts = true;
        auto push = Def(GirOp::Push, 2);
        push.a = 0;
        push.b = 1;
        push.org = 0;
        auto pop = Def(GirOp::Pop, 3);
        pop.a = 0;
        pop.org = 0;
        touch.blocks = { { { { 0, reference } }, { Int(m, 1, "7"), push, pop, Ret() } } };
        GirFunc wrapper = touch;
        wrapper.name = "wrapper";
        auto call = Def(GirOp::Call, 1);
        call.idx = 1;
        call.vals = { 0 };
        call.org = 0;
        wrapper.blocks = { { { { 0, reference } }, { call, Ret() } } };
        m.funcs.push_back(std::move(touch));
        m.funcs.push_back(std::move(wrapper));
        assert(Code(m) == "");
        for (int field = 0; field < 4; field++) {
            auto omitted = m;
            auto &summary = omitted.funcs[2].summary;
            vector<vector<CoreTarget> *> fields { &summary.reads, &summary.writes, &summary.grows, &summary.shrinks };
            fields[field]->clear();
            assert(Code(omitted) == "GIR-V050");
        }
    }
}

GirModule ConstructionNamedAliasModule();

GirModule ConstructionNamedGrowAsPackedResultModule() {
    auto m = ConstructionNamedAliasModule();
    auto grow = Main(m).slots[0].ty;
    CoreType packed;
    packed.kind = CoreType::VarArr;
    packed.elem = m.Type(grow).elem;
    auto packedType = m.Intern(packed);
    Main(m).slots[0].ty = packedType;
    Main(m).blocks[0].insts[2].ty = packedType;
    Main(m).blocks[0].insts[2].knownCount.reset();
    auto &callee = m.funcs[1];
    callee.results[0] = packedType;
    callee.blocks[0].params[0].second = m.CarrierType(CoreType::Dest, packedType, CoreRequest::Value);
    auto local = Def(GirOp::Slot, 4);
    local.idx = 0;
    auto append = Def(GirOp::Push, 6);
    append.a = 4;
    append.b = 5;
    append.org = 0;
    auto sample = Def(GirOp::Snap, 7);
    sample.a = 4;
    sample.snap = GirSnapshotMode::Owner;
    auto render = Def(GirOp::Render, 8);
    render.a = 7;
    render.org = 0;
    GirInst print;
    print.op = GirOp::Print;
    print.parts = { { false, {}, 8 } };
    print.org = 0;
    auto &instructions = callee.blocks[0].insts;
    auto beforeNamed = find_if(instructions.begin(), instructions.end(), [](auto &inst) { return inst.op == GirOp::DestNamed; });
    instructions.insert(beforeNamed, { local, Int(m, 5, "9"), append, sample, render, print });
    callee.summary.outputs = true;
    auto slot = Def(GirOp::Slot, 3);
    slot.idx = 0;
    auto output = Def(GirOp::Snap, 4);
    output.a = 3;
    output.snap = GirSnapshotMode::Owner;
    auto outputRender = Def(GirOp::Render, 5);
    outputRender.a = 4;
    outputRender.org = 0;
    print.parts[0].val = 5;
    auto &caller = Main(m).blocks[0].insts;
    caller.insert(caller.end() - 2, { slot, output, outputRender, print });
    Main(m).summary.outputs = true;
    return m;
}

void ConstructionNamedGrowAliasesReserveTheReceivingPrefix() {
    auto high = ConstructionNamedGrowAsPackedResultModule();
    assert(Code(high) == "");
    assert(Code(GirToLow(high).Lower()) == "");
    auto wrong = high;
    wrong.funcs[1].slots[0].ty = wrong.IntType(CoreIntTy::I64);
    assert(Code(wrong) == "GIR-V010");
}

CoreModule ConstructionSourceTargetModule() {
    CoreModule core;
    core.profile = CoreProfile::Construction;
    core.files = { "source-target.goose" };
    core.types = { CoreType { .kind = CoreType::Int, .ity = CoreIntTy::I64 },
                   CoreType { .kind = CoreType::Grow, .elem = 0 }, CoreType { .kind = CoreType::Unit } };
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Expr };
    CoreImpl entry;
    entry.name = "main";
    entry.body.scope = 0;
    entry.vars = { CoreVar { "out", 1, CoreVarKind::Let, 0, origin } };
    auto call = make_unique<CoreExpr>();
    call->kind = CoreExprKind::Call;
    call->ctx = 1;
    call->type = 1;
    call->org = origin;
    CoreStmt receive;
    receive.kind = CoreStmtKind::Let;
    receive.var = 0;
    receive.expr = std::move(call);
    receive.org = origin;
    entry.body.stmts.push_back(std::move(receive));
    CoreImpl target;
    target.name = "target";
    target.body.scope = 0;
    target.results = { CoreResultDescriptor { 1, CoreRequest::Value, nullopt } };
    target.summary.constructs = { 0 };
    auto helperCall = make_unique<CoreExpr>();
    helperCall->kind = CoreExprKind::Call;
    helperCall->ctx = 2;
    helperCall->type = 2;
    helperCall->org = origin;
    CoreStmt invoke;
    invoke.kind = CoreStmtKind::Expr;
    invoke.expr = std::move(helperCall);
    invoke.org = origin;
    target.body.stmts.push_back(std::move(invoke));
    CoreImpl helper;
    helper.name = "helper";
    helper.body.scope = 0;
    helper.summary.needs = { 0 };
    helper.summary.escapes = { 0 };
    auto array = make_unique<CoreExpr>();
    array->kind = CoreExprKind::Arr;
    array->type = 1;
    array->org = origin;
    auto element = make_unique<CoreExpr>();
    element->kind = CoreExprKind::Lit;
    element->type = 0;
    element->value = "7";
    array->elems.push_back(std::move(element));
    CoreStmt escape;
    escape.kind = CoreStmtKind::ReturnFrom;
    escape.target = 0;
    escape.values.push_back(std::move(array));
    escape.org = origin;
    helper.body.stmts.push_back(std::move(escape));
    core.impls.push_back(std::move(entry));
    core.impls.push_back(std::move(target));
    core.impls.push_back(std::move(helper));
    core.contexts = { CoreContext { .impl = 0 }, CoreContext { .impl = 1 }, CoreContext { .impl = 2 } };
    core.targets = { CoreTargetSet { { 1 } } };
    return core;
}

void ConstructionSourceTargetsLowerToCheckedReceivingEdges() {
    auto core = ConstructionSourceTargetModule();
    auto high = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Expr } },
        [](const CoreOrigin &) { return 0; }).Lower();
    assert(Code(high) == "");
    assert(GirWriter(high).Write().find("t_invoke") != string::npos);
    assert(GirWriter(high).Write().find("t_escape") != string::npos);
    bool unsupported = false;
    try {
        auto low = GirToLow(high).Lower();
        assert(low.lowtargets.size() == 1);
        assert(Code(low) == "");
        assert(GirWriter(low).WriteLow().find("[\"lchannel\",0,") != string::npos);

        auto unusedPayload = low;
        auto targetFunction = low.lowtargets[0].members[0];
        auto &targetBody = unusedPayload.funcs[targetFunction];
        auto normalDispatch = find_if(targetBody.blocks[0].insts.begin(), targetBody.blocks[0].insts.end(),
            [](const GirInst &inst) { return inst.op == GirOp::CondBr; });
        assert(normalDispatch != targetBody.blocks[0].insts.end());
        auto targetDispatch = normalDispatch->idx2;
        auto hit = unusedPayload.funcs[targetFunction].blocks[targetDispatch].insts.back().idx;
        auto &handler = unusedPayload.funcs[targetFunction].blocks[hit];
        auto payloadUse = find_if(handler.insts.begin(), handler.insts.end(), [](const GirInst &inst) {
            return inst.op == GirOp::Br;
        });
        assert(payloadUse != handler.insts.end() && payloadUse->vals.size() >= 2);
        auto savedStart = find_if(targetBody.blocks[0].insts.begin(), targetBody.blocks[0].insts.end(),
            [](const GirInst &inst) { return inst.op == GirOp::TargetLoad && inst.idx == 0 && inst.idx2 == 4; });
        assert(savedStart != targetBody.blocks[0].insts.end());
        payloadUse->vals[1] = savedStart->res;
        assert(Code(unusedPayload) == "GIR-V090");

        auto missingPosition = low;
        missingPosition.lowtargets[0].channels[0].position = -1;
        assert(Code(missingPosition) == "GIR-V090");

        auto duplicatePosition = low;
        duplicatePosition.lowtargets[0].channels.push_back(duplicatePosition.lowtargets[0].channels[0]);
        assert(Code(duplicatePosition) == "GIR-V090");

        auto missingActivation = low;
        auto &missingEntry = missingActivation.funcs[targetFunction].blocks[0].insts;
        auto active = find_if(missingEntry.begin(), missingEntry.end(), [](const GirInst &inst) {
            return inst.op == GirOp::TargetStore && inst.idx == 0 && inst.idx2 == 0;
        });
        assert(active != missingEntry.end());
        missingEntry.erase(active);
        assert(!Code(missingActivation).empty());

        auto duplicateActivation = low;
        auto &duplicateEntry = duplicateActivation.funcs[targetFunction].blocks[0].insts;
        auto activeStore = find_if(duplicateEntry.begin(), duplicateEntry.end(), [](const GirInst &inst) {
            return inst.op == GirOp::TargetStore && inst.idx == 0 && inst.idx2 == 0;
        });
        assert(activeStore != duplicateEntry.end());
        duplicateEntry.insert(activeStore, *activeStore);
        assert(!Code(duplicateActivation).empty());

        auto missingDispatch = low;
        auto duplicateDispatch = low;
        auto missingHandler = low;
        for (auto &block : missingDispatch.funcs[targetFunction].blocks) {
            auto *term = GirIsTerminator(block.insts.back().op) ? &block.insts.back() : nullptr;
            if (!term || term->op != GirOp::CondBr) continue;
            for (auto &inst : block.insts) if (inst.op == GirOp::Call && inst.idx == 2) {
                auto dispatch = term->idx2;
                auto *caseTerm = &missingDispatch.funcs[targetFunction].blocks[dispatch].insts.back();
                assert(caseTerm && caseTerm->op == GirOp::CondBr);
                caseTerm->op = GirOp::Br;
                caseTerm->idx2 = -1;
                goto missing_dispatch_changed;
            }
        }
missing_dispatch_changed:
        assert(!Code(missingDispatch).empty());

        for (auto &block : duplicateDispatch.funcs[targetFunction].blocks) {
            auto *term = GirIsTerminator(block.insts.back().op) ? &block.insts.back() : nullptr;
            if (!term || term->op != GirOp::CondBr) continue;
            for (auto &inst : block.insts) if (inst.op == GirOp::Call && inst.idx == 2) {
                auto dispatch = term->idx2;
                auto &caseBlock = duplicateDispatch.funcs[targetFunction].blocks[dispatch];
                for (auto &compare : caseBlock.insts) if (compare.op == GirOp::Cmp && compare.cmp == CoreCmpOp::Eq) {
                    auto tag = compare.b;
                    for (auto &definition : caseBlock.insts) if (definition.res == tag && definition.op == GirOp::Int)
                        definition.text = "0";
                }
                goto duplicate_dispatch_changed;
            }
        }
duplicate_dispatch_changed:
        assert(!Code(duplicateDispatch).empty());

        for (auto &block : missingHandler.funcs[targetFunction].blocks) {
            auto *term = GirIsTerminator(block.insts.back().op) ? &block.insts.back() : nullptr;
            if (!term || term->op != GirOp::CondBr) continue;
            for (auto &inst : block.insts) if (inst.op == GirOp::Call && inst.idx == 2) {
                auto dispatch = term->idx2;
                auto *caseTerm = &missingHandler.funcs[targetFunction].blocks[dispatch].insts.back();
                assert(caseTerm && caseTerm->op == GirOp::CondBr);
                caseTerm->idx = caseTerm->idx2;
                goto missing_handler_changed;
            }
        }
missing_handler_changed:
        assert(!Code(missingHandler).empty());
    } catch (const GirLowerUnsupported &) {
        unsupported = true;
    }
    assert(!unsupported);
    auto forged = high;
    forged.funcs[2].blocks[0].insts.back().op = GirOp::Ret;
    forged.funcs[2].blocks[0].insts.back().vals.clear();
    forged.funcs[2].blocks[0].insts.back().vals2.clear();
    assert(Code(forged) == "GIR-V020");
    auto differentEdge = high;
    for (auto &block : differentEdge.funcs[1].blocks) for (auto &inst : block.insts)
        if (inst.op == GirOp::Invoke) inst.escapes[0].block = inst.a;
    assert(Code(differentEdge) == "GIR-V020");
}

void ConstructionReturnFlagsFollowCalls() {
    auto core = ConstructionSourceTargetModule();
    auto high = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Expr } },
        [](const CoreOrigin &) { return 0; }).Lower();
    auto low = GirToLow(high).Lower();
    assert(Code(low) == "");
    auto i64 = low.IntType(CoreIntTy::I64);
    GirFunc ordinary;
    ordinary.name = "ordinary";
    ordinary.params = { i64 };
    ordinary.scopes = { -1 };
    GirInst setNormal;
    setNormal.op = GirOp::ReturnFlagSet;
    setNormal.a = 1;
    ordinary.blocks = { GirBlock { { { 0, i64 } }, { Int(low, 1, "0"), setNormal, Ret() } } };
    low.funcs.push_back(ordinary);
    GirInst call;
    call.op = GirOp::Call;
    call.idx = 3;
    call.vals = { 0 };
    call.org = 0;
    auto &escape = low.funcs[2].blocks[0].insts;
    auto flag = find_if(escape.begin(), escape.end(), [](const GirInst &inst) {
        return inst.op == GirOp::ReturnFlagSet;
    });
    assert(flag != escape.end());
    escape.insert(flag + 1, call);
    assert(!Code(low).empty());
}

void ConstructionPointerEqualityRejectsTraceMetadata() {
    auto low = ConstructionAliasedProvenanceModule();
    auto &function = Main(low);
    int valueCount = 0;
    for (auto &block : function.blocks) {
        valueCount += (int)block.params.size();
        for (auto &inst : block.insts) valueCount += GirDefinesValue(inst);
    }
    auto comparison = Def(GirOp::PtrEq, valueCount);
    comparison.a = 1;
    comparison.b = 1;
    auto &instructions = function.blocks[0].insts;
    instructions.insert(instructions.end() - 2, comparison);
    assert(Code(low) == "");
    instructions[instructions.size() - 3].a = 4;
    assert(Code(low) == "GIR-V090");
}

GirModule ConstructionMixedReferenceResultModule() {
    auto m = ConstructionReturnedReferenceCopyModule();
    auto &callee = m.funcs[1];
    auto integer = m.IntType(CoreIntTy::I64);
    callee.results.insert(callee.results.begin(), integer);
    callee.resultProtocols.insert(callee.resultProtocols.begin(), GirResultProtocol {});
    callee.roots.results.insert(callee.roots.results.begin(), vector<CoreRootRef> {});
    auto &instructions = callee.blocks[0].insts;
    instructions.insert(instructions.begin() + 2, Int(m, 1, "7"));
    instructions.back() = Ret({ 1, 0 });
    auto &caller = Main(m).blocks[0].insts;
    auto projection = Def(GirOp::Result, 8);
    projection.a = 6;
    projection.idx = 1;
    for (size_t position = 0; position < caller.size(); position++)
        if (caller[position].op == GirOp::DestCopy) {
            caller[position].b = 8;
            caller.insert(caller.begin() + position, projection);
            break;
        }
    return m;
}

void ConstructionReferenceProvenanceUsesEachResultPosition() {
    auto high = ConstructionMixedReferenceResultModule();
    assert(Code(high) == "");
    assert(Code(GirToLow(high).Lower()) == "");
    high.funcs[1].roots.results[1].clear();
    assert(Code(high) == "GIR-V050");
}

GirModule ConstructionAdaptedCallModule(bool receivingVariable) {
    auto m = ConstructionCallModule();
    auto grow = Main(m).slots[0].ty;
    CoreType variable;
    variable.kind = CoreType::VarArr;
    variable.elem = m.Type(grow).elem;
    auto variableType = m.Intern(variable);
    auto receiving = receivingVariable ? variableType : grow;
    auto producer = receivingVariable ? grow : variableType;
    Main(m).slots[0].ty = receiving;
    auto &callee = m.funcs[1];
    callee.results[0] = producer;
    callee.blocks[0].params[0].second = m.CarrierType(CoreType::Dest, producer, CoreRequest::Value);
    auto open = Main(m).blocks[0].insts[2];
    open.ty = receiving;
    auto adapt = Def(GirOp::DestAdapt, 2);
    adapt.a = 1;
    adapt.ty = producer;
    adapt.request = CoreRequest::Value;
    adapt.org = 0;
    auto call = Main(m).blocks[0].insts[3];
    call.res = 3;
    call.vals2 = { 2 };
    auto restore = Def(GirOp::DestAdaptFinish, 4);
    restore.a = 3;
    restore.org = 0;
    auto publish = Main(m).blocks[0].insts[4];
    publish.a = 4;
    auto slot = Def(GirOp::Slot, 5);
    slot.idx = 0;
    auto sample = Def(GirOp::Snap, 6);
    sample.a = 5;
    sample.snap = GirSnapshotMode::Owner;
    auto render = Def(GirOp::Render, 7);
    render.a = 6;
    render.org = 0;
    GirInst print;
    print.op = GirOp::Print;
    print.parts = { { false, {}, 7 } };
    print.org = 0;
    Main(m).summary.outputs = true;
    Main(m).blocks[0].insts = { Enter(0), Int(m, 0, "1"), open, adapt, call, restore, publish,
                              slot, sample, render, print, Leave(0), Ret() };
    return m;
}

void ConstructionAdaptersRestoreExactCompletionAndCancellation() {
    for (bool receivingVariable : { false, true }) {
        auto m = ConstructionAdaptedCallModule(receivingVariable);
        assert(Code(m) == "");
        assert(GirWriter(m).Write().find("i_dest_adapt_finish") != string::npos);
        auto low = GirToLow(m).Lower();
        assert(Code(low) == "");
        m = ConstructionAdaptedCallModule(receivingVariable);
        Main(m).blocks[0].insts[5].a = 1;
        assert(Code(m) == "GIR-V010");
        m = ConstructionAdaptedCallModule(receivingVariable);
        Main(m).blocks[0].insts[3].request = CoreRequest::Register;
        assert(Code(m) == "GIR-V010");
        m = ConstructionAdaptedCallModule(receivingVariable);
        Main(m).blocks[0].insts[4].vals2 = { 1 };
        assert(Code(m) == "GIR-V010");
        m = ConstructionAdaptedCallModule(receivingVariable);
        auto reuse = Def(GirOp::DestAbandon, 8);
        reuse.a = 1;
        reuse.org = 0;
        Main(m).blocks[0].insts.insert(Main(m).blocks[0].insts.begin() + 4, reuse);
        assert(Code(m) == "GIR-V060");
        m = ConstructionAdaptedCallModule(receivingVariable);
        auto abandon = Def(GirOp::DestAbandon, 3);
        abandon.a = 2;
        abandon.org = 0;
        Main(m).blocks[0].insts[4] = abandon;
        Main(m).blocks[0].insts[6].op = GirOp::DestCancel;
        Main(m).blocks[0].insts.resize(7);
        Main(m).blocks[0].insts.push_back(Leave(0));
        Main(m).blocks[0].insts.push_back(Ret());
        m.funcs.resize(1);
        assert(Code(m) == "");
        assert(Code(GirToLow(m).Lower()) == "");
        Main(m).blocks[0].insts[6].a = 3;
        assert(Code(m) == "GIR-V060");
    }
}

GirModule ConstructionNamedAliasModule() {
    auto m = ConstructionCallModule();
    auto &callee = m.funcs[1];
    callee.slots = { { callee.results[0], CoreVarKind::Var, 0, 0 } };
    callee.resultProtocols[0].namedSlot = 0;
    GirInst bind;
    bind.op = GirOp::DestBind;
    bind.idx = 0;
    bind.a = 2;
    bind.org = 0;
    auto named = Def(GirOp::DestNamed, 3);
    named.idx = 0;
    named.org = 0;
    auto &instructions = callee.blocks[0].insts;
    instructions.insert(instructions.begin() + 4, bind);
    instructions.insert(instructions.begin() + 5, named);
    instructions.back() = Ret({ 3 });
    return m;
}

void ConstructionNamedAliasesUseTheIncomingStack() {
    auto high = ConstructionNamedAliasModule();
    assert(Code(high) == "");
    auto low = GirToLow(high).Lower();
    assert(Code(low) == "");
    assert(low.funcs[1].stacks == 0);
    int initialization = 0;
    for (auto &block : low.funcs[1].blocks) for (auto &inst : block.insts) initialization += inst.op == GirOp::HdrInit;
    assert(initialization == 1);
    for (auto &block : low.funcs[1].blocks) for (auto &inst : block.insts)
        if (inst.op == GirOp::HdrInit) inst.b = inst.a;
    assert(Code(low) == "GIR-V090");
}

GirModule ConstructionPushReferenceModule() {
    auto m = Base();
    m.profile = CoreProfile::Construction;
    auto byte = m.IntType(CoreIntTy::U8);
    CoreType inner;
    inner.kind = CoreType::VarArr;
    inner.elem = byte;
    auto innerType = m.Intern(inner);
    CoreType outer;
    outer.kind = CoreType::Grow;
    outer.elem = innerType;
    auto outerType = m.Intern(outer);
    Main(m).slots = { { outerType, CoreVarKind::Let, 0, 0 } };
    Main(m).summary.aborts = true;
    Main(m).summary.outputs = true;
    auto empty = Def(GirOp::DestOpen, 1);
    empty.ty = outerType;
    empty.knownCount = 0;
    empty.destReceiver = GirDestSlotReceiver { 0 };
    empty.org = 0;
    auto finishEmpty = Def(GirOp::DestFinish, 2);
    finishEmpty.a = 1;
    GirInst publishEmpty;
    publishEmpty.op = GirOp::DestPublish;
    publishEmpty.a = 2;
    publishEmpty.org = 0;
    auto owner = Def(GirOp::Slot, 3);
    owner.idx = 0;
    auto push = Def(GirOp::DestOpen, 4);
    push.ty = innerType;
    push.destReceiver = GirDestPushReceiver { 3 };
    push.org = 0;
    GirInst bytes;
    bytes.op = GirOp::DestBytes;
    bytes.a = 4;
    bytes.bytes = { 65 };
    bytes.org = 0;
    auto finish = Def(GirOp::DestFinish, 5);
    finish.a = 4;
    auto reference = Def(GirOp::DestPublishRef, 6);
    reference.a = 5;
    reference.org = 0;
    auto sample = Def(GirOp::Snap, 7);
    sample.a = 6;
    auto element = Def(GirOp::Elem, 9);
    element.a = 7;
    element.b = 8;
    element.org = 0;
    auto value = Def(GirOp::Int, 10);
    value.ty = byte;
    value.text = "66";
    GirInst store;
    store.op = GirOp::Store;
    store.a = 9;
    store.b = 10;
    store.org = 0;
    auto length = Def(GirOp::ArrayLen, 11);
    length.a = 3;
    auto render = Def(GirOp::Render, 12);
    render.a = 11;
    render.org = 0;
    auto sampleAgain = Def(GirOp::Snap, 13);
    sampleAgain.a = 6;
    auto byteReference = Def(GirOp::Elem, 14);
    byteReference.a = 13;
    byteReference.b = 8;
    byteReference.org = 0;
    auto load = Def(GirOp::Load, 15);
    load.a = 14;
    auto renderByte = Def(GirOp::Render, 16);
    renderByte.a = 15;
    renderByte.org = 0;
    GirInst print;
    print.op = GirOp::Print;
    print.parts = { { false, {}, 12 }, { true, " ", -1 }, { false, {}, 16 } };
    print.org = 0;
    Main(m).blocks[0].insts = { Enter(0), Int(m, 0, "0"), empty, finishEmpty, publishEmpty,
        owner, push, bytes, finish, reference, sample, Int(m, 8, "0"), element, value, store,
        length, render, sampleAgain, byteReference, load, renderByte, print, Leave(0), Ret() };
    return m;
}

void ConstructionPushPublishesOneMutableElementReference() {
    auto high = ConstructionPushReferenceModule();
    assert(Code(high) == "");
    auto low = GirToLow(high).Lower();
    assert(Code(low) == "");
    int beginnings = 0, publications = 0;
    for (auto &function : low.funcs) for (auto &block : function.blocks) for (auto &inst : block.insts) {
        beginnings += inst.op == GirOp::Event && inst.event == GirEventKind::Begin;
        publications += inst.op == GirOp::Event && inst.event == GirEventKind::Publish;
    }
    assert(beginnings == 2 && publications == 2);
    auto &instructions = Main(high).blocks[0].insts;
    instructions[6].destReceiver = GirDestSlotReceiver { 0 };
    instructions[6].ty = Main(high).slots[0].ty;
    assert(Code(high) == "GIR-V010");
}

void ConstructionPrintSnapshotsHaveOneResumedConsumer() {
    auto high = ConstructionPushReferenceModule();
    auto &instructions = Main(high).blocks[0].insts;
    auto print = find_if(instructions.begin(), instructions.end(), [](auto &inst) { return inst.op == GirOp::Print; });
    print->parts.push_back(print->parts[0]);
    assert(Code(high) == "GIR-V060");
    high = ConstructionPushReferenceModule();
    auto &unconsumed = Main(high).blocks[0].insts;
    unconsumed.erase(find_if(unconsumed.begin(), unconsumed.end(), [](auto &inst) { return inst.op == GirOp::Print; }));
    assert(Code(high) == "GIR-V060");
}

int main() {
    ConstructionPrintSnapshotsHaveOneResumedConsumer();
    ConstructionNamedGrowAliasesReserveTheReceivingPrefix();
    ConstructionSourceTargetsLowerToCheckedReceivingEdges();
    ConstructionReturnFlagsFollowCalls();
    ConstructionPointerEqualityRejectsTraceMetadata();
    ConstructionReferenceProvenanceUsesEachResultPosition();
    ConstructionPushPublishesOneMutableElementReference();
    ConstructionAdaptersRestoreExactCompletionAndCancellation();
    ConstructionNamedAliasesUseTheIncomingStack();
    StorageSummaryCoverageNormalizesSpecializedAndGenericRoots();
    ConstructionReturnedReferenceRetainsCopyProvenance();
    ConstructionProvenanceShadowsDistinguishAliasedArguments();
    ConstructionRecursiveArraysUseExplicitPackedTraversal();
    ConstructionCallsAndCarrierBranchesLowerToPrimitiveChannels();
    ConstructionFixedResultsUseExplicitOutputChannels();
    ConstructionVariableExitRequiresCancellationBeforeLanding();
    ConstructionTargetEdgesAreTypedAndDerivedFromBodies();
    ConstructionCallsReturnTheTransferredChannel();
    ConstructionCarrierOwnershipCrossesBranchParameters();
    ConstructionAbandonmentProducesOneCancellationCertificate();
    ConstructionLowOperationsRetainExactByteAndEventWire();
    ConstructionLowFormattingChecksScalarKind();
    Accepts();
    EvidenceProvesFixedIndexAndRejectsForgedProofs();
    EvidenceDoesNotMergeDifferentBlockParameters();
    EvidenceDropsAddressesAcrossScopeReentry();
    NonI64ComparisonDoesNotProveIndex();
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
    SpecializedParameterSummariesNormalizeBothCoverageSides();
    RejectsParameterRootUnderapproximationAtCall();
    AcceptsUnreachableAfterANonReturningCall();
    RejectsUnreachableWithoutANonReturningCall();
    RejectsAbortingOperationWithoutOrigin();
    LowAccepts();
    RejectsHighOperationInLowModule();
    RejectsConstructionTargetsInLowModule();
    RejectsTwoResizablesOnOneStack();
    RejectsWatermarkPastCallerOwnedRegion();
    PassedOwnerPairsKeepTheirExactIdentity();
    OwnerCallUsesReturnedPairOnlyAfterOneProvenCall();
    ReturnedOwnerPairRequiresEveryReturnAndMatchingStores();
    ReturnedOwnerPairRejectsUnsafePhiCycles();
    RecursiveOwnerReturnDoesNotSeedItsOwnProof();
    RejectsReplacementThroughALetOwnerPhi();
    LowPreservesOwnerLiteralRunsAcrossJoins();
    LowSplitsSameTargetCondBrForOwnerRuns();
    RejectsInvalidShrinkReplacementProofs();
    RejectsUnresolvedLayout();
    RejectsElementsThatDoNotTopTheirStack();
    PilotAndShrinkModuleShapesStayDistinct();
    CoreShrinkPushAndSummaryCarryOriginsAndShrinks();
    DirectOwnerLengthsUseArrayLength();
    CoreShrinkOperationTagsAndPlaceTypingAreCanonical();
    CoreShrinkOperationsLowerToVerifiedGir();
    ResizeChecksFollowNegativeSizeAndEvaluateFillFirst();
    LimitedAppendChecksCapacityBeforeWriting();
    AggregatePopCopiesBeforeReleasingItsStack();
    LimitedClearStoresItsLengthInByteStorage();
    PilotPushWithoutOriginLowersToValidLowGir();
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
    LowLimitedOwnerAccessUsesByteCopies();
    NestedStructAndFixedArrayFieldsUseByteStorage();
    LowAggregateLoopParametersOwnSnapshots();
    AcceptsNestedFieldContentsThroughAJoin();
    RejectsArrayElementWriteThroughConstFieldContents();
    FieldProjectionKeepsItsOwnerRoot();
    FieldProjectionKeepsGlobalReadAndWriteEffects();
    FieldCallArgumentsKeepTheirOwnerRoot();
    AcceptsEmptyOwnerFactsThroughBlockParameters();
    RejectsPassingAReadOnlyStructFieldToAMutatingCall();
    OwnerArrayElementsRemainWritable();
    OwnerGrowElementsRemainWritable();
    MutableSliceCallResultsRemainWritable();
    MutableSliceParametersRemainWritable();
    RejectsReturningAFieldRefFromAReadOnlyOwner();
    RejectsMaterializingAFieldRefFromAReadOnlyOwner();
    RejectsPassingAContentsConstAggregateFieldToAMutatingCall();
    LowKeepsPackedFieldAlignmentAcrossCallParametersAndResults();
    ConstructionBytesUseLinearDestinationProtocol();
    ConstructionBytesRejectIncompleteOrMismatchedDestinations();
    ConstructionGrowArrayUsesElementDestinations();
    ConstructionWholeAssignmentUsesOwnerDestination();
    ConstructionRejectsDetachedGrowArrayAggregates();
    ConstructionTargetsRejectEmptyAndRepeatedMemberSets();
    puts("compiler_gir ok");
    return 0;
}
