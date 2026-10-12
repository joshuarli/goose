// The GIR-H verifier on small modules built in memory: a module the lowering
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
#include "../src/core/core_ir.h"
#include "../src/core/core_json.h"
#include "../src/gir/gir_ir.h"
#include "../src/gir/gir_types.h"
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

}  // namespace

int main() {
    Accepts();
    RejectsUseNotDominatedByDefinition();
    RejectsWrongEdgeArgumentType();
    RejectsBlockWithTwoTerminatorsOrNone();
    RejectsStoreThroughConst();
    RejectsSlotAddressOutsideItsScope();
    RejectsUnbalancedScopesOnOnePath();
    RejectsReturnInsideAnEnteredScope();
    RejectsSummaryThatOmitsAWrite();
    RejectsAbortingOperationWithoutOrigin();
    puts("compiler_gir ok");
    return 0;
}
