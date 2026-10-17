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

GirInst Inst(GirOp op, int result = -1, int a = -1, int b = -1) {
    GirInst instruction;
    instruction.op = op;
    instruction.res = result;
    instruction.a = a;
    instruction.b = b;
    instruction.org = 0;
    return instruction;
}

GirModule Module() {
    GirModule module;
    module.files = { "store-effects.goose" };
    module.origins = { { 0, 1, CoreOriginKind::Let } };
    GirFunc entry;
    entry.name = "main";
    entry.scopes = { -1 };
    entry.blocks = { { {}, { Inst(GirOp::Ret) } } };
    module.funcs = { entry };
    return module;
}

string Code(GirModule module) {
    auto violation = GirVerifier(module).Verify();
    return violation ? violation->code : "";
}

GirModule ContentAliasStore() {
    auto module = Module();
    auto integer = module.IntType(CoreIntTy::I64);
    auto slice = module.SliceType(CoreMut::Mut, integer);
    auto reference = module.RefType(CoreMut::Mut, integer);
    auto sliceReference = module.RefType(CoreMut::Mut, slice);
    GirFunc caller;
    caller.name = "flat_content_store";
    caller.params = { slice };
    caller.slots = { { slice, CoreVarKind::Var, 0, 0 } };
    caller.scopes = { -1 };
    caller.summary.writes = { { false, 0 } };
    caller.summary.reads = { { false, 0 } };
    caller.summary.aborts = true;
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto init = Inst(GirOp::Init, -1, 0);
    init.idx = 0;
    auto slot = Inst(GirOp::Slot, 1);
    slot.idx = 0;
    auto call = Inst(GirOp::Call, 2);
    call.idx = 2;
    call.vals = { 1, 0 };
    auto literal = Inst(GirOp::Int, 3);
    literal.ty = integer;
    literal.text = "1";
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    caller.blocks = { { { { 0, slice } },
        { enter, init, slot, call, literal, Inst(GirOp::Store, -1, 2, 3), leave, Inst(GirOp::Ret) } } };
    module.funcs.push_back(caller);
    GirFunc callee;
    callee.name = "content_alias";
    callee.params = { sliceReference, slice };
    callee.results = { reference };
    callee.scopes = { -1 };
    callee.roots.contents = { { 0, { { CoreRootRef::Param, 0 }, { CoreRootRef::Param, 1 } } } };
    callee.roots.results = { { { CoreRootRef::Param, 0 }, { CoreRootRef::Param, 1 } } };
    callee.summary.reads = { { false, 0 } };
    auto zero = Inst(GirOp::Int, 4);
    zero.ty = integer;
    zero.text = "0";
    auto ret = Inst(GirOp::Ret);
    ret.vals = { 5 };
    callee.blocks = { { { { 0, sliceReference }, { 1, slice } },
        { Inst(GirOp::Load, 2, 0), Inst(GirOp::SliceView, 3, 2), zero,
          Inst(GirOp::Elem, 5, 3, 4), ret } } };
    module.funcs.push_back(callee);
    return module;
}

GirModule ParameterContentStore() {
    auto module = ContentAliasStore();
    auto &callee = module.funcs[2];
    callee.roots.contents[0].second = { { CoreRootRef::Param, 0 } };
    callee.results.clear();
    callee.roots.results.clear();
    callee.summary.writes = { { false, 0 } };
    auto literal = Inst(GirOp::Int, 6);
    literal.ty = module.IntType(CoreIntTy::I64);
    literal.text = "1";
    auto &instructions = callee.blocks[0].insts;
    instructions.pop_back();
    instructions.push_back(literal);
    instructions.push_back(Inst(GirOp::Store, -1, 5, 6));
    instructions.push_back(Inst(GirOp::Ret));
    module.funcs.erase(module.funcs.begin() + 1);
    return module;
}

GirModule LocalBindingStore(bool reference) {
    auto module = Module();
    auto integer = module.IntType(CoreIntTy::I64);
    auto type = reference ? module.RefType(CoreMut::Mut, integer) : module.SliceType(CoreMut::Mut, integer);
    GirFunc function;
    function.name = reference ? "reference_binding_store" : "slice_binding_store";
    function.params = { type, type };
    function.slots = { { type, CoreVarKind::Var, 0, 0 }, { type, CoreVarKind::Let, 0, 1 } };
    function.scopes = { -1 };
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto init = Inst(GirOp::Init, -1, 0);
    init.idx = 0;
    auto address = Inst(GirOp::Slot, 2);
    address.idx = 0;
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    function.blocks = { { { { 0, type }, { 1, type } },
        { enter, init, address, Inst(GirOp::Store, -1, 2, 1), leave, Inst(GirOp::Ret) } } };
    module.funcs.push_back(function);
    return module;
}

GirModule SliceParameterBindingStore() {
    auto module = Module();
    auto slice = module.SliceType(CoreMut::Mut, module.IntType(CoreIntTy::I64));
    auto reference = module.RefType(CoreMut::Mut, slice);
    GirFunc function;
    function.name = "slice_parameter_binding_store";
    function.params = { reference, slice };
    function.scopes = { -1 };
    function.roots.contents = { { 0, { { CoreRootRef::Param, 1 } } } };
    function.summary.writes = { { false, 0 } };
    function.blocks = { { { { 0, reference }, { 1, slice } },
        { Inst(GirOp::Store, -1, 0, 1), Inst(GirOp::Ret) } } };
    module.funcs.push_back(function);
    return module;
}

void RequiresRebind(GirModule module) {
    auto violation = GirVerifier(module).Verify();
    assert(violation && violation->code == "GIR-V050");
    assert(violation->message == cat("function ", module.funcs[1].name,
        " rebinds parameter 0, which its summary omits"));
    module.funcs[1].summary.rebinds = { { false, 0 } };
    assert(Code(module).empty());
}

}

int main() {
    assert(Code(ContentAliasStore()).empty());
    assert(Code(ParameterContentStore()).empty());
    RequiresRebind(LocalBindingStore(false));
    RequiresRebind(LocalBindingStore(true));
    RequiresRebind(SliceParameterBindingStore());
}
