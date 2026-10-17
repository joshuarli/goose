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

GirModule EmptyContentReplacement() {
    auto module = Module();
    module.profile = CoreProfile::Shrink;
    auto integer = module.IntType(CoreIntTy::I64);
    auto slice = module.SliceType(CoreMut::Const, integer);
    auto reference = module.RefType(CoreMut::Const, slice);
    auto owner = module.Intern(CoreType { .kind = CoreType::GrowShrink, .elem = integer });
    GirFunc function;
    function.name = "replace_after_empty_content_length";
    function.params = { reference };
    function.slots = { { reference, CoreVarKind::Let, 0, 0 }, { owner, CoreVarKind::Var, 0, 1 } };
    function.scopes = { -1 };
    function.summary.unknown = true;
    function.roots.params = { { 0, { { CoreRootRef::Param, 0 } } } };
    function.roots.contents = { { 0, {} } };
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto empty = Inst(GirOp::Arr, 1);
    empty.ty = owner;
    auto init = Inst(GirOp::Init, -1, 1);
    init.idx = 1;
    auto address = Inst(GirOp::Slot, 2);
    address.idx = 1;
    auto run = Inst(GirOp::Arr, 6);
    run.ty = owner;
    run.vals = { 5 };
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    function.blocks = { { { { 0, reference } },
        { enter, empty, init, address, Inst(GirOp::Clear, -1, 2), Inst(GirOp::Load, 3, 0),
          Inst(GirOp::SliceView, 4, 3), Inst(GirOp::ViewLen, 5, 4), run,
          Inst(GirOp::Replace, -1, 2, 6), leave, Inst(GirOp::Ret) } } };
    module.funcs.push_back(function);
    return module;
}

void AcceptsReplacementAfterKnownEmptyContentRead() {
    auto module = EmptyContentReplacement();
    assert(Code(module).empty());
    module.funcs[1].roots.contents.clear();
    assert(Code(module) == "GIR-V050");
}

GirModule LocalEmptyContentReplacement(bool initialize = true) {
    auto module = EmptyContentReplacement();
    auto slice = module.Type(module.funcs[1].params[0]).elem;
    auto &function = module.funcs[1];
    function.slots.push_back({ slice, CoreVarKind::Let, 0, 2 });
    auto &instructions = function.blocks[0].insts;
    auto address = Inst(GirOp::Slot, 7);
    address.idx = 2;
    instructions.insert(instructions.begin() + 6, { address, Inst(GirOp::Load, 8, 7) });
    if (initialize) {
        auto init = Inst(GirOp::Init, -1, 3);
        init.idx = 2;
        instructions.insert(instructions.begin() + 6, init);
    }
    for (auto &instruction : instructions)
        if (instruction.op == GirOp::SliceView) instruction.a = 8;
    return module;
}

void PreservesKnownEmptyLocalCopies() {
    assert(Code(LocalEmptyContentReplacement()).empty());
    assert(Code(LocalEmptyContentReplacement(false)) == "GIR-V060");
}

void RequiresEveryJoinInputKnownEmpty() {
    auto module = EmptyContentReplacement();
    auto slice = module.Type(module.funcs[1].params[0]).elem;
    auto &function = module.funcs[1];
    auto &instructions = function.blocks[0].insts;
    GirBlock join;
    join.params = { { 7, slice } };
    join.insts.assign(instructions.begin() + 6, instructions.end());
    join.insts[0].a = 7;
    instructions.erase(instructions.begin() + 6, instructions.end());
    auto branch = Inst(GirOp::Br);
    branch.idx = 1;
    branch.vals = { 3 };
    instructions.push_back(branch);
    function.blocks.push_back(join);
    assert(Code(module).empty());

    function.slots.push_back({ slice, CoreVarKind::Let, 0, 2 });
    auto unknownAddress = Inst(GirOp::Slot, 8);
    unknownAddress.idx = 2;
    auto &entry = function.blocks[0].insts;
    entry.insert(entry.begin() + 4, { unknownAddress, Inst(GirOp::Load, 9, 8) });
    auto condition = Inst(GirOp::Bool, 10);
    entry.insert(entry.end() - 1, condition);
    auto &choice = entry.back();
    choice.op = GirOp::CondBr;
    choice.a = 10;
    choice.idx2 = 1;
    choice.vals2 = { 9 };
    assert(Code(module) == "GIR-V060");

    choice = Inst(GirOp::Br);
    choice.idx = 1;
    choice.vals = { 9 };
    auto &loop = function.blocks[1].insts;
    GirBlock exit;
    exit.insts.assign(loop.end() - 2, loop.end());
    loop.erase(loop.end() - 2, loop.end());
    auto repeat = Inst(GirOp::CondBr, -1, 10);
    repeat.idx = 1;
    repeat.idx2 = 2;
    repeat.vals = { 7 };
    loop.push_back(repeat);
    function.blocks.push_back(exit);
    assert(Code(module) == "GIR-V060");
}

GirModule GlobalEmptyContentReplacement() {
    auto module = EmptyContentReplacement();
    auto owner = module.funcs[1].slots[1].ty;
    GirGlobal global;
    global.name = "owner";
    global.ty = owner;
    global.kind = CoreVarKind::Var;
    global.init.name = "owner_init";
    global.init.results = { owner };
    global.init.scopes = { -1 };
    auto empty = Inst(GirOp::Arr, 0);
    empty.ty = owner;
    auto ret = Inst(GirOp::Ret);
    ret.vals = { 0 };
    global.init.blocks = { { {}, { empty, ret } } };
    module.globals.push_back(global);
    auto &function = module.funcs[1];
    swap(function.blocks[0].insts[4], function.blocks[0].insts[5]);
    for (auto &instruction : function.blocks[0].insts)
        if (instruction.res == 2) {
            instruction.op = GirOp::Global;
            instruction.idx = 0;
        }
    return module;
}

void RetainsNonemptyContentAliases() {
    auto module = GlobalEmptyContentReplacement();
    assert(Code(module).empty());
    module.funcs[1].roots.contents[0].second = { { CoreRootRef::Global, 0 } };
    assert(Code(module) == "GIR-V060");
}

void RejectsChangedEmptyParameterContents() {
    for (bool aliased : { false, true })
        for (bool called : { false, true }) {
            auto module = GlobalEmptyContentReplacement();
            auto slice = module.Type(module.funcs[1].params[0]).elem;
            auto reference = module.RefType(CoreMut::Mut, slice);
            auto &function = module.funcs[1];
            if (!aliased) {
                function.params[0] = reference;
                function.slots[0].ty = reference;
                function.blocks[0].params[0].second = reference;
            }
            function.params.push_back(slice);
            function.roots.params.push_back({ 1, { { CoreRootRef::Global, 0 } } });
            function.blocks[0].params.push_back({ 7, slice });
            int address = 0;
            if (aliased) {
                function.params.push_back(reference);
                function.roots.params.push_back({ 2, { { CoreRootRef::Param, 2 } } });
                function.blocks[0].params.push_back({ 8, reference });
                address = 8;
            }
            auto write = Inst(GirOp::Store, -1, address, 7);
            if (called) {
                write = Inst(GirOp::Call);
                write.idx = 2;
                write.vals = { address, 7 };
            }
            function.blocks[0].insts.insert(function.blocks[0].insts.begin() + 4, write);
            if (called) {
                GirFunc callee;
                callee.name = "replace_parameter_contents";
                callee.params = { reference, slice };
                callee.scopes = { -1 };
                callee.summary.unknown = true;
                callee.blocks = { { { { 0, reference }, { 1, slice } },
                    { Inst(GirOp::Store, -1, 0, 1), Inst(GirOp::Ret) } } };
                module.funcs.push_back(callee);
            }
            assert(Code(module) == "GIR-V060");
            if (called) {
                module.funcs[2].summary.unknown = false;
                module.funcs[2].summary.writes = { { false, 0 } };
                module.funcs[2].summary.rebinds = { { false, 0 } };
                assert(Code(module) == "GIR-V060");
            }
            module.funcs[1].roots.params[1].second.clear();
            assert(Code(module).empty());
        }
}

void RejectsGlobalContentChangesFromNoArgumentCalls() {
    auto module = GlobalEmptyContentReplacement();
    auto slice = module.Type(module.funcs[1].params[0]).elem;
    GirGlobal global;
    global.name = "slice_header";
    global.ty = slice;
    global.kind = CoreVarKind::Var;
    global.init.name = "slice_header_init";
    global.init.results = { slice };
    global.init.scopes = { -1 };
    global.init.summary.unknown = true;
    global.init.roots.results = { { { CoreRootRef::Global, 0 } } };
    auto owner = Inst(GirOp::Global, 0);
    owner.idx = 0;
    auto view = Inst(GirOp::Snap, 1, 0);
    auto content = Inst(GirOp::ViewSlice, 2, 1);
    content.mut = CoreMut::Const;
    auto ret = Inst(GirOp::Ret);
    ret.vals = { 2 };
    global.init.blocks = { { {}, { owner, view, content, ret } } };
    module.globals.push_back(global);
    GirFunc callee;
    callee.name = "change_global_slice_header";
    callee.scopes = { -1 };
    callee.summary.unknown = true;
    auto header = Inst(GirOp::Global, 3);
    header.idx = 1;
    callee.blocks = { { {}, { owner, view, content, header, Inst(GirOp::Store, -1, 3, 2), Inst(GirOp::Ret) } } };
    module.funcs.push_back(callee);
    auto &function = module.funcs[1];
    function.roots.params[0].second = { { CoreRootRef::Global, 1 } };
    auto call = Inst(GirOp::Call);
    call.idx = 2;
    function.blocks[0].insts.insert(function.blocks[0].insts.begin() + 4, call);
    assert(Code(module) == "GIR-V060");
    module.funcs[2].summary.unknown = false;
    module.funcs[2].summary.aborts = true;
    module.funcs[2].summary.reads = { { true, 0 } };
    module.funcs[2].summary.writes = { { true, 1 } };
    assert(Code(module) == "GIR-V060");
}

void PreservesConservativeCallDependencies() {
    auto local = LocalEmptyContentReplacement();
    auto slice = local.Type(local.funcs[1].params[0]).elem;
    auto reference = local.funcs[1].params[0];
    auto integer = local.IntType(CoreIntTy::I64);
    auto addCall = [&](GirModule module, vector<int> arguments, vector<int> types) {
        GirFunc callee;
        callee.name = "unused_arguments";
        callee.params = types;
        callee.scopes = { -1 };
        GirBlock entry;
        for (int index = 0; index < (int)types.size(); index++) entry.params.push_back({ index, types[index] });
        entry.insts = { Inst(GirOp::Ret) };
        callee.blocks = { entry };
        module.funcs.push_back(callee);
        auto call = Inst(GirOp::Call);
        call.idx = 2;
        call.vals = arguments;
        auto &instructions = module.funcs[1].blocks[0].insts;
        auto position = find_if(instructions.begin(), instructions.end(), [](const GirInst &instruction) {
            return instruction.op == GirOp::Replace;
        });
        instructions.insert(position, call);
        return module;
    };
    assert(Code(addCall(local, { 5 }, { integer })).empty());
    assert(Code(addCall(local, { 3 }, { slice })).empty());
    assert(Code(addCall(local, { 7 }, { reference })) == "GIR-V060");
    assert(Code(addCall(local, { 7, 3 }, { reference, slice })).empty());

    auto opaque = EmptyContentReplacement();
    GirFunc callee;
    callee.name = "opaque_slice";
    callee.results = { slice };
    callee.roots.results = { {} };
    callee.scopes = { -1 };
    callee.summary.aborts = true;
    callee.blocks = { { {}, { Inst(GirOp::Abort) } } };
    opaque.funcs.push_back(callee);
    auto call = Inst(GirOp::Call, 7);
    call.idx = 2;
    auto &instructions = opaque.funcs[1].blocks[0].insts;
    instructions.insert(instructions.begin() + 6, call);
    for (auto &instruction : instructions)
        if (instruction.op == GirOp::SliceView) instruction.a = 7;
    assert(Code(opaque) == "GIR-V060");
}

}

int main() {
    AcceptsReplacementAfterKnownEmptyContentRead();
    PreservesKnownEmptyLocalCopies();
    RequiresEveryJoinInputKnownEmpty();
    RetainsNonemptyContentAliases();
    RejectsChangedEmptyParameterContents();
    RejectsGlobalContentChangesFromNoArgumentCalls();
    PreservesConservativeCallDependencies();
    assert(Code(ContentAliasStore()).empty());
    assert(Code(ParameterContentStore()).empty());
    RequiresRebind(LocalBindingStore(false));
    RequiresRebind(LocalBindingStore(true));
    RequiresRebind(SliceParameterBindingStore());
}
