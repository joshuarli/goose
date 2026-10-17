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

void AcceptsStoresBetweenEmptyParameterContents() {
    auto module = EmptyContentReplacement();
    auto slice = module.Type(module.funcs[1].params[0]).elem;
    auto reference = module.RefType(CoreMut::Mut, slice);
    auto &function = module.funcs[1];
    function.params = { reference, reference };
    function.slots[0].ty = reference;
    function.blocks[0].params = { { 0, reference }, { 7, reference } };
    function.roots.params.push_back({ 1, { { CoreRootRef::Param, 1 } } });
    function.roots.contents.push_back({ 1, {} });
    auto &instructions = function.blocks[0].insts;
    instructions.insert(instructions.begin() + 4, { Inst(GirOp::Load, 8, 7), Inst(GirOp::Store, -1, 0, 8) });
    assert(Code(module).empty());
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
            assert(Code(module) == (called ? "GIR-V060" : ""));
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

void RejectsGlobalContentChangesWithUnusedEmptyArgument() {
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
    callee.params = { slice };
    callee.roots.params = { { 0, {} } };
    callee.blocks[0].params = { { 4, slice } };
    module.funcs.push_back(callee);
    auto &function = module.funcs[1];
    function.roots.params[0].second = { { CoreRootRef::Global, 1 } };
    function.params.push_back(slice);
    function.roots.params.push_back({ 1, {} });
    function.blocks[0].params.push_back({ 7, slice });
    auto call = Inst(GirOp::Call);
    call.vals = { 7 };
    call.idx = 2;
    function.blocks[0].insts.insert(function.blocks[0].insts.begin() + 4, call);
    assert(Code(module) == "GIR-V060");
    module.funcs[2].summary.unknown = false;
    module.funcs[2].summary.aborts = true;
    module.funcs[2].summary.reads = { { true, 0 } };
    module.funcs[2].summary.writes = { { true, 1 } };
    assert(Code(module) == "GIR-V060");
    module.funcs[2].roots.params[0].second = { { CoreRootRef::Global, 1 } };
    module.funcs[2].summary.writes = { { false, 0 } };
    assert(Code(module) == "GIR-V060");
    module.funcs[2].roots.params[0].second = { { CoreRootRef::Param, 0 }, { CoreRootRef::Global, 1 } };
    auto local = Inst(GirOp::Slot, 8);
    local.idx = 1;
    auto localView = Inst(GirOp::Snap, 9, 8);
    auto localSlice = Inst(GirOp::ViewSlice, 10, 9);
    localSlice.mut = CoreMut::Const;
    auto &instructions = module.funcs[1].blocks[0].insts;
    auto position = find_if(instructions.begin(), instructions.end(), [](const GirInst &instruction) {
        return instruction.op == GirOp::Call;
    });
    position->vals = { 10 };
    instructions.insert(position, { local, localView, localSlice });
    assert(Code(module) == "GIR-V060");
}

void RejectsLocalContentChangesWithUnusedEmptyArgument() {
    for (int initialRoots : { 0, 1, 2 }) {
        auto module = LocalEmptyContentReplacement();
        auto slice = module.Type(module.funcs[1].params[0]).elem;
        auto reference = module.RefType(CoreMut::Mut, slice);
        auto &function = module.funcs[1];
        function.slots[2].kind = CoreVarKind::Var;
        if (initialRoots != 0) {
            function.params.push_back(slice);
            function.roots.params.push_back({ 1, {} });
            function.blocks[0].params.push_back({ 11, slice });
            for (auto &instruction : function.blocks[0].insts)
                if (instruction.op == GirOp::Init && instruction.idx == 2) instruction.a = 11;
        }
        auto &instructions = function.blocks[0].insts;
        auto clear = instructions[4];
        instructions.erase(instructions.begin() + 4);
        auto position = find_if(instructions.begin(), instructions.end(), [](const GirInst &instruction) {
            return instruction.op == GirOp::Load && instruction.res == 8;
        });
        auto view = Inst(GirOp::Snap, 9, 2);
        auto alias = Inst(GirOp::ViewSlice, 10, 9);
        alias.mut = CoreMut::Const;
        auto call = Inst(GirOp::Call);
        call.idx = 2;
        call.vals = { 7, 3, 10, initialRoots ? 11 : 3 };
        instructions.insert(position, { view, alias, call, clear });
        GirFunc callee;
        callee.name = "replace_local_holder";
        callee.params = { reference, slice, slice, slice };
        callee.roots.contents = { { 0, { { CoreRootRef::Param, 1 }, { CoreRootRef::Param, 2 }, { CoreRootRef::Param, 3 } } } };
        callee.scopes = { -1 };
        callee.summary.writes = { { false, 0 } };
        callee.summary.rebinds = { { false, 0 } };
        callee.blocks = { { { { 0, reference }, { 1, slice }, { 2, slice }, { 3, slice } },
            { Inst(GirOp::Store, -1, 0, 2), Inst(GirOp::Ret) } } };
        module.funcs.push_back(callee);
        if (initialRoots == 2) {
            module.globals = GlobalEmptyContentReplacement().globals;
            module.funcs[1].roots.params[1].second = { { CoreRootRef::Global, 0 } };
            module.funcs[2].roots.contents[0].second.push_back({ CoreRootRef::Global, 0 });
        }
        assert(Code(module) == "GIR-V060");
        module.funcs[2].summary.unknown = true;
        assert(Code(module) == "GIR-V060");
        module.funcs[2].blocks[0].insts[0].b = 1;
        assert(Code(module).empty());
    }
}

GirModule UnknownCallGraphReplacement(int count, bool cycle, bool mutates) {
    auto module = mutates ? GlobalEmptyContentReplacement() : EmptyContentReplacement();
    auto integer = module.IntType(CoreIntTy::I64);
    for (int index = 0; index < count; index++) {
        GirFunc callee;
        callee.name = cat("unknown_call_", index);
        callee.params = { integer };
        callee.scopes = { -1 };
        callee.summary.unknown = true;
        GirBlock entry;
        entry.params = { { 0, integer } };
        if (index + 1 < count || cycle) {
            auto call = Inst(GirOp::Call);
            call.idx = index + 1 < count ? index + 3 : 2;
            call.vals = { 0 };
            entry.insts.push_back(call);
        }
        if (mutates && index + 1 == count) {
            auto address = Inst(GirOp::Global, 1);
            address.idx = 0;
            entry.insts.push_back(address);
            entry.insts.push_back(Inst(GirOp::Push, 2, 1, 0));
        }
        entry.insts.push_back(Inst(GirOp::Ret));
        callee.blocks = { entry };
        module.funcs.push_back(callee);
    }
    auto call = Inst(GirOp::Call);
    call.idx = 2;
    call.vals = { 5 };
    auto &instructions = module.funcs[1].blocks[0].insts;
    auto position = find_if(instructions.begin(), instructions.end(), [](const GirInst &instruction) {
        return instruction.op == GirOp::Replace;
    });
    instructions.insert(position, call);
    return module;
}

void CertifiesUnknownMemoryFreeCallGraphs() {
    assert(Code(UnknownCallGraphReplacement(1, false, false)).empty());
    assert(Code(UnknownCallGraphReplacement(3, false, false)).empty());
    assert(Code(UnknownCallGraphReplacement(3, true, false)).empty());
    assert(Code(UnknownCallGraphReplacement(3, false, true)) == "GIR-V060");
    assert(Code(UnknownCallGraphReplacement(3, true, true)) == "GIR-V060");
    auto module = UnknownCallGraphReplacement(1, false, false);
    module.globals = GlobalEmptyContentReplacement().globals;
    auto &instructions = module.funcs[1].blocks[0].insts;
    swap(instructions[4], instructions[5]);
    for (auto &instruction : instructions)
        if (instruction.res == 2) {
            instruction.op = GirOp::Global;
            instruction.idx = 0;
        }
    assert(Code(module).empty());
    module.funcs[2].summary.unknown = false;
    module.funcs[2].summary.writes = { { true, 0 } };
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
    assert(Code(addCall(local, { 7 }, { reference })).empty());
    auto unknownPure = addCall(local, { 7 }, { reference });
    unknownPure.funcs[2].summary.unknown = true;
    assert(Code(unknownPure).empty());
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
    assert(Code(opaque).empty());
    opaque.funcs[2].roots.results.clear();
    assert(Code(opaque) == "GIR-V060");
}


void RetainsSpecializedGlobalPolicyWithEmptyActualArguments() {
    auto module = GlobalEmptyContentReplacement();
    auto slice = module.Type(module.funcs[1].params[0]).elem;
    module.funcs[1].params.push_back(slice);
    module.funcs[1].blocks[0].params.push_back({ 7, slice });
    module.funcs[1].roots.params.push_back({ 1, {} });
    GirFunc callee;
    callee.name = "pure_with_global_policy";
    callee.params = { slice };
    callee.roots.params = { { 0, { { CoreRootRef::Global, 0 } } } };
    callee.summary.writes = { { false, 0 } };
    callee.scopes = { -1 };
    callee.blocks = { { { { 0, slice } }, { Inst(GirOp::Ret) } } };
    module.funcs.push_back(callee);
    auto call = Inst(GirOp::Call);
    call.idx = 2;
    call.vals = { 7 };
    auto &instructions = module.funcs[1].blocks[0].insts;
    instructions.insert(instructions.end() - 3, call);
    assert(Code(module) == "GIR-V060");
    module.funcs[2].roots.params[0].second.clear();
    assert(Code(module).empty());
}

GirGlobal IntegerGlobal(GirModule &module) {
    auto integer = module.IntType(CoreIntTy::I64);
    GirGlobal global;
    global.ty = integer;
    global.kind = CoreVarKind::Var;
    global.init.name = "integer_global";
    global.init.results = { integer };
    global.init.scopes = { -1 };
    auto zero = Inst(GirOp::Int, 0);
    zero.ty = integer;
    zero.text = "0";
    auto ret = Inst(GirOp::Ret);
    ret.vals = { 0 };
    global.init.blocks = { { {}, { zero, ret } } };
    return global;
}

void PreservesActualGlobalCallDependencies() {
    for (bool writes : { false, true }) {
        auto module = EmptyContentReplacement();
        module.globals.push_back(IntegerGlobal(module));
        GirFunc callee;
        callee.name = "unknown_global_access";
        callee.summary.unknown = true;
        callee.scopes = { -1 };
        auto address = Inst(GirOp::Global, 0);
        address.idx = 0;
        vector<GirInst> body = { address, Inst(GirOp::Load, 1, 0) };
        if (writes) body.push_back(Inst(GirOp::Store, -1, 0, 1));
        body.push_back(Inst(GirOp::Ret));
        callee.blocks = { { {}, body } };
        module.funcs.push_back(callee);
        auto call = Inst(GirOp::Call);
        call.idx = 2;
        auto &instructions = module.funcs[1].blocks[0].insts;
        instructions.insert(instructions.end() - 3, call);
        assert(Code(module).empty());
        auto &caller = module.funcs[1];
        auto receiverType = module.RefType(CoreMut::Mut, caller.slots[1].ty);
        caller.params.push_back(receiverType);
        caller.blocks[0].params.push_back({ 7, receiverType });
        caller.roots.params[0].second.clear();
        for (auto &inst : caller.blocks[0].insts)
            if (inst.op == GirOp::Clear || inst.op == GirOp::Replace) inst.a = 7;
        assert(Code(module).empty());
        module.funcs[2].summary.unknown = false;
        module.funcs[2].summary.reads = { { true, 0 } };
        if (writes) module.funcs[2].summary.writes = { { true, 0 } };
        assert(Code(module) == "GIR-V060");
        auto scalarReference = module.RefType(CoreMut::Mut, module.globals[0].ty);
        module.funcs[2].params = { scalarReference };
        module.funcs[2].blocks = { { { { 0, scalarReference } }, { Inst(GirOp::Load, 1, 0), Inst(GirOp::Ret) } } };
        module.funcs[2].summary = {};
        module.funcs[2].summary.unknown = true;
        auto globalAddress = Inst(GirOp::Global, 8);
        globalAddress.idx = 0;
        auto &callerBody = caller.blocks[0].insts;
        auto position = find_if(callerBody.begin(), callerBody.end(), [](const GirInst &inst) { return inst.op == GirOp::Call; });
        position->vals = { 8 };
        callerBody.insert(position, globalAddress);
        assert(Code(module) == "GIR-V060");
    }
}

void CertifiesRecursiveReferenceReturnBounds() {
    auto module = EmptyContentReplacement();
    auto slice = module.Type(module.funcs[1].params[0]).elem;
    GirFunc callee;
    callee.name = "recursive_reference";
    callee.results = { slice };
    callee.roots.results = { {} };
    callee.summary.unknown = true;
    callee.scopes = { -1 };
    auto recursive = Inst(GirOp::Call, 0);
    recursive.idx = 2;
    auto ret = Inst(GirOp::Ret);
    ret.vals = { 0 };
    callee.blocks = { { {}, { recursive, ret } } };
    module.funcs.push_back(callee);
    auto call = Inst(GirOp::Call, 7);
    call.idx = 2;
    auto &instructions = module.funcs[1].blocks[0].insts;
    instructions.insert(instructions.begin() + 6, call);
    for (auto &instruction : instructions)
        if (instruction.op == GirOp::SliceView) instruction.a = 7;
    assert(Code(module).empty());
    module.funcs[2].roots.results.clear();
    assert(Code(module) == "GIR-V060");
}

enum class OwnerReferenceForm { DirectCall, LocalCopyCall };
enum class OwnerReferenceUse { Unused, Read, Length };

CoreModule OwnerReferenceReplacement(bool dependent, OwnerReferenceUse use, OwnerReferenceForm form = OwnerReferenceForm::DirectCall) {
    CoreModule core;
    core.profile = CoreProfile::Shrink;
    core.files = { "owner-reference-replacement.goose" };
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Expr };
    auto integer = core.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::GrowShrink;
    owner.elem = integer;
    auto ownerType = core.Intern(owner);
    CoreType reference;
    reference.kind = CoreType::Ref;
    reference.mut = CoreMut::Const;
    reference.elem = ownerType;
    auto referenceType = core.Intern(reference);
    int target = dependent ? 0 : 1;
    for (auto name : { "owner", "other" }) {
        CoreGlobal global;
        global.name = name;
        global.type = ownerType;
        global.kind = CoreVarKind::Var;
        global.org = origin;
        global.init = make_unique<CoreExpr>();
        global.init->kind = CoreExprKind::Arr;
        global.init->type = ownerType;
        core.globals.push_back(std::move(global));
    }
    CoreImpl main;
    main.name = "main";
    main.vars = { { "q", referenceType, CoreVarKind::Let, 1, origin } };
    main.summary.unknown = true;
    CoreStmt assignment;
    assignment.kind = CoreStmtKind::AssignWhole;
    assignment.org = origin;
    assignment.place = make_unique<CorePlace>();
    assignment.place->kind = CorePlace::Global;
    assignment.expr = make_unique<CoreExpr>();
    assignment.expr->kind = CoreExprKind::Arr;
    assignment.expr->type = ownerType;
    auto block = make_unique<CoreExpr>();
    block->kind = CoreExprKind::Block;
    block->then = make_unique<CoreBlock>();
    block->then->scope = 1;
    CoreStmt bind;
    bind.kind = CoreStmtKind::Let;
    bind.var = 0;
    bind.org = origin;
    bind.expr = make_unique<CoreExpr>();
    bind.expr->kind = CoreExprKind::Call;
    bind.expr->ctx = 1;
    bind.expr->org = origin;
    block->then->stmts.push_back(std::move(bind));
    block->then->value = make_unique<CoreExpr>();
    if (use == OwnerReferenceUse::Length) {
        auto &value = *block->then->value;
        value.kind = CoreExprKind::Len;
        value.view = make_unique<CoreView>();
        value.view->place = make_unique<CorePlace>();
        value.view->place->kind = CorePlace::Deref;
        value.view->place->expr = make_unique<CoreExpr>();
        value.view->place->expr->kind = CoreExprKind::Read;
        value.view->place->expr->place = make_unique<CorePlace>();
    } else {
        block->then->value->kind = CoreExprKind::Lit;
        block->then->value->type = integer;
        block->then->value->value = "0";
    }
    if (use == OwnerReferenceUse::Read) {
        CoreStmt read;
        read.kind = CoreStmtKind::Expr;
        read.org = origin;
        read.expr = make_unique<CoreExpr>();
        read.expr->kind = CoreExprKind::Read;
        read.expr->place = make_unique<CorePlace>();
        block->then->stmts.push_back(std::move(read));
    }
    assignment.expr->elems.push_back(std::move(block));
    main.body.stmts.push_back(std::move(assignment));
    core.impls.push_back(std::move(main));
    CoreContext mainContext;
    mainContext.impl = 0;
    mainContext.varroots = { { 0, { { CoreRootRef::Global, target } } } };
    core.contexts.push_back(std::move(mainContext));
    CoreImpl callee;
    callee.name = "owner_address";
    callee.results = { { referenceType } };
    callee.body.value = make_unique<CoreExpr>();
    callee.body.value->kind = CoreExprKind::Ref;
    callee.body.value->mut = CoreMut::Const;
    callee.body.value->place = make_unique<CorePlace>();
    callee.body.value->place->kind = CorePlace::Global;
    callee.body.value->place->index = target;
    if (form == OwnerReferenceForm::LocalCopyCall) {
        callee.vars = { { "r", referenceType, CoreVarKind::Let, 0, origin } };
        CoreStmt bind;
        bind.kind = CoreStmtKind::Let;
        bind.var = 0;
        bind.org = origin;
        bind.expr = std::move(callee.body.value);
        callee.body.stmts.push_back(std::move(bind));
        callee.body.value = make_unique<CoreExpr>();
        callee.body.value->kind = CoreExprKind::Read;
        callee.body.value->place = make_unique<CorePlace>();
    }
    core.impls.push_back(std::move(callee));
    CoreContext calleeContext;
    calleeContext.impl = 1;
    calleeContext.resultroots = { { { CoreRootRef::Global, target } } };
    if (form == OwnerReferenceForm::LocalCopyCall) calleeContext.varroots = { { 0, { { CoreRootRef::Global, target } } } };
    core.contexts.push_back(std::move(calleeContext));
    return core;
}

void DistinguishesReturnedOwnerAddressesFromReads() {
    for (auto form : { OwnerReferenceForm::DirectCall, OwnerReferenceForm::LocalCopyCall })
        for (bool dependent : { true, false })
            for (auto use : { OwnerReferenceUse::Unused, OwnerReferenceUse::Read, OwnerReferenceUse::Length }) {
                auto core = OwnerReferenceReplacement(dependent, use, form);
                auto gir = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Expr } },
                    [](const CoreOrigin &) { return 0; }).Lower();
                auto observed = Code(gir);
                auto expected = dependent && use != OwnerReferenceUse::Unused ? "GIR-V060" : "";
                if (observed != expected)
                    fprintf(stderr, "owner return dependent=%d use=%d form=%d: %s\n",
                        dependent, (int)use, (int)form, observed.c_str());
                assert(observed == expected);
            }
}

void LowersCrossParameterContentBounds() {
    CoreModule core;
    core.profile = CoreProfile::Shrink;
    core.files = { "cross-parameter-content.goose" };
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Let };
    auto integer = core.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::GrowShrink;
    owner.elem = integer;
    auto ownerType = core.Intern(owner);
    CoreType slice;
    slice.kind = CoreType::Slice;
    slice.mut = CoreMut::Mut;
    slice.elem = core.BoolType();
    auto sliceType = core.Intern(slice);
    CoreType reference;
    reference.kind = CoreType::Ref;
    reference.mut = CoreMut::Mut;
    reference.elem = sliceType;
    auto referenceType = core.Intern(reference);
    CoreImpl main;
    main.name = "main";
    main.summary.unknown = true;
    main.vars = { { "owner", ownerType, CoreVarKind::Var, 0, origin } };
    CoreStmt initial;
    initial.kind = CoreStmtKind::Let;
    initial.var = 0;
    initial.org = origin;
    initial.expr = make_unique<CoreExpr>();
    initial.expr->kind = CoreExprKind::Arr;
    initial.expr->type = ownerType;
    main.body.stmts.push_back(std::move(initial));
    CoreStmt replacement;
    replacement.kind = CoreStmtKind::AssignWhole;
    replacement.org = origin;
    replacement.place = make_unique<CorePlace>();
    replacement.expr = make_unique<CoreExpr>();
    replacement.expr->kind = CoreExprKind::Arr;
    replacement.expr->type = ownerType;
    auto zero = make_unique<CoreExpr>();
    zero->kind = CoreExprKind::Read;
    zero->place = make_unique<CorePlace>();
    zero->place->kind = CorePlace::Global;
    zero->place->index = 0;
    replacement.expr->elems.push_back(std::move(zero));
    CoreGlobal global;
    global.name = "scalar";
    global.type = integer;
    global.org = origin;
    global.init = make_unique<CoreExpr>();
    global.init->kind = CoreExprKind::Lit;
    global.init->type = integer;
    global.init->value = "0";
    core.globals.push_back(std::move(global));
    main.body.stmts.push_back(std::move(replacement));
    core.impls.push_back(std::move(main));
    CoreContext mainContext;
    mainContext.impl = 0;
    core.contexts.push_back(std::move(mainContext));
    for (int index : { 1, 2 }) {
        CoreImpl function;
        function.name = index == 1 ? "wrapper" : "callee";
        function.params = { { 0, true }, { 1, true } };
        function.vars = { { "a", referenceType, CoreVarKind::Let, 0, origin },
                          { "b", referenceType, CoreVarKind::Let, 0, origin } };
        function.summary.unknown = true;
        if (index == 1) {
            CoreStmt call;
            call.kind = CoreStmtKind::Expr;
            call.org = origin;
            call.expr = make_unique<CoreExpr>();
            call.expr->kind = CoreExprKind::Call;
            call.expr->ctx = 2;
            call.expr->org = origin;
            for (int variable : { 0, 1 }) {
                auto dereference = make_unique<CorePlace>();
                dereference->kind = CorePlace::Deref;
                dereference->expr = make_unique<CoreExpr>();
                dereference->expr->kind = CoreExprKind::Read;
                dereference->expr->place = make_unique<CorePlace>();
                dereference->expr->place->index = variable;
                call.expr->args.push_back(CoreArgReference { CoreMut::Mut, std::move(dereference) });
            }
            function.body.stmts.push_back(std::move(call));
        }
        core.impls.push_back(std::move(function));
        CoreContext context;
        context.impl = index;
        context.varroots = { { 0, { { CoreRootRef::Param, 0 } } }, { 1, { { CoreRootRef::Param, 1 } } } };
        context.content = { { { CoreRootRef::Param, 1 } }, {} };
        context.hascontent = { 1, 1 };
        core.contexts.push_back(std::move(context));
    }
    auto gir = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
    assert(Code(gir).empty());
    gir.funcs[2].roots.contents[0].second.clear();
    assert(Code(gir) == "GIR-V050");
    CoreImpl writer;
    writer.name = "independent_writer";
    writer.params = { { 0, true }, { 1, true }, { 2, false } };
    writer.vars = { { "a", referenceType, CoreVarKind::Let, 0, origin },
                    { "b", referenceType, CoreVarKind::Let, 0, origin },
                    { "value", sliceType, CoreVarKind::Let, 0, origin } };
    writer.summary.unknown = true;
    CoreStmt assignment;
    assignment.kind = CoreStmtKind::Assign;
    assignment.org = origin;
    assignment.place = make_unique<CorePlace>();
    assignment.place->kind = CorePlace::Deref;
    assignment.place->expr = make_unique<CoreExpr>();
    assignment.place->expr->kind = CoreExprKind::Read;
    assignment.place->expr->place = make_unique<CorePlace>();
    assignment.expr = make_unique<CoreExpr>();
    assignment.expr->kind = CoreExprKind::Read;
    assignment.expr->place = make_unique<CorePlace>();
    assignment.expr->place->index = 2;
    writer.body.stmts.push_back(std::move(assignment));
    core.impls.push_back(std::move(writer));
    CoreContext writerContext;
    writerContext.impl = 3;
    writerContext.varroots = { { 0, { { CoreRootRef::Param, 0 } } }, { 1, { { CoreRootRef::Param, 1 } } },
                              { 2, { { CoreRootRef::Param, 2 } } } };
    writerContext.content = { { { CoreRootRef::Param, 2 } }, {}, {} };
    writerContext.hascontent = { 1, 1, 0 };
    core.contexts.push_back(std::move(writerContext));
    auto independent = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
    assert(Code(independent).empty());
}

GirModule ActualHolderAliasModule(bool aliased) {
    auto module = GlobalEmptyContentReplacement();
    auto other = module.globals[0];
    other.name = "other_owner";
    module.globals.push_back(other);
    auto slice = module.Type(module.funcs[1].params[0]).elem;
    auto mutableReference = module.RefType(CoreMut::Mut, slice);
    auto &callee = module.funcs[1];
    callee.params.push_back(mutableReference);
    callee.params.push_back(slice);
    callee.blocks[0].params.push_back({ 7, mutableReference });
    callee.blocks[0].params.push_back({ 8, slice });
    callee.roots.params.push_back({ 1, { { CoreRootRef::Param, 1 } } });
    callee.roots.params.push_back({ 2, { { CoreRootRef::Global, 0 } } });
    callee.roots.contents[0].second = { { CoreRootRef::Global, 1 } };
    callee.roots.contents.push_back({ 1, { { CoreRootRef::Global, 0 }, { CoreRootRef::Global, 1 } } });
    callee.blocks[0].insts.insert(callee.blocks[0].insts.begin() + 4, Inst(GirOp::Store, -1, 7, 8));
    auto &entry = module.funcs[0];
    entry.summary.unknown = true;
    entry.slots = { { slice, CoreVarKind::Var, 0, 0 }, { slice, CoreVarKind::Var, 0, 1 } };
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto global = Inst(GirOp::Global, 0);
    global.idx = 1;
    auto initial = Inst(GirOp::ViewSlice, 2, 1);
    initial.mut = CoreMut::Const;
    auto firstInit = Inst(GirOp::Init, -1, 2);
    firstInit.idx = 0;
    auto secondInit = firstInit;
    secondInit.idx = 1;
    auto first = Inst(GirOp::Slot, 3);
    first.idx = 0;
    auto second = Inst(GirOp::Slot, 4);
    second.idx = 1;
    auto receiver = Inst(GirOp::Global, 5);
    receiver.idx = 0;
    auto payload = Inst(GirOp::ViewSlice, 7, 6);
    payload.mut = CoreMut::Const;
    auto call = Inst(GirOp::Call);
    call.idx = 1;
    call.vals = { 3, aliased ? 3 : 4, 7 };
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    entry.blocks[0].insts = { enter, global, Inst(GirOp::Snap, 1, 0), initial, firstInit, secondInit,
        first, second, receiver, Inst(GirOp::Snap, 6, 5), payload, call, leave, Inst(GirOp::Ret) };
    return module;
}

void AdmitsCallerStorageThroughGenericContentBounds() {
    auto module = GlobalEmptyContentReplacement();
    for (int index : { 1, 2 }) {
        auto global = module.globals[0];
        global.name = cat("content_owner", index);
        module.globals.push_back(std::move(global));
    }
    auto owner = module.globals[0].ty;
    auto integer = module.Type(owner).elem;
    auto slice = module.SliceType(CoreMut::Const, integer);
    auto holder = module.RefType(CoreMut::Mut, slice);
    auto &caller = module.funcs[1];
    caller.params.clear();
    caller.roots = {};
    caller.slots = { { slice, CoreVarKind::Var, 0, 0 } };
    caller.summary.unknown = true;
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto address = [](int value, int global) { auto inst = Inst(GirOp::Global, value); inst.idx = global; return inst; };
    auto initial = Inst(GirOp::ViewSlice, 3, 2);
    initial.mut = CoreMut::Const;
    auto slot = Inst(GirOp::Slot, 4);
    slot.idx = 0;
    auto initialize = Inst(GirOp::Init, -1, 3);
    initialize.idx = 0;
    auto payload = Inst(GirOp::ViewSlice, 7, 6);
    payload.mut = CoreMut::Const;
    auto write = Inst(GirOp::Call);
    write.idx = 2;
    write.vals = { 4, 7 };
    auto read = Inst(GirOp::Call);
    read.idx = 3;
    read.vals = { 4, 3 };
    auto zero = Inst(GirOp::Int, 8);
    zero.ty = integer;
    zero.text = "0";
    auto literal = Inst(GirOp::Arr, 9);
    literal.ty = owner;
    literal.vals = { 8 };
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    caller.blocks = { { {}, { enter, address(0, 0), address(1, 1), Inst(GirOp::Snap, 2, 1), initial,
        slot, initialize, address(5, 2), Inst(GirOp::Snap, 6, 5), payload, write,
        Inst(GirOp::Clear, -1, 0), read, zero, literal, Inst(GirOp::Replace, -1, 0, 9), leave, Inst(GirOp::Ret) } } };
    GirFunc writer;
    writer.name = "content_writer";
    writer.params = { holder, slice };
    writer.scopes = { -1 };
    writer.summary.unknown = true;
    writer.roots.contents = { { 0, { { CoreRootRef::Global, 1 }, { CoreRootRef::Param, 1 } } } };
    writer.blocks = { { { { 0, holder }, { 1, slice } }, { Inst(GirOp::Store, -1, 0, 1), Inst(GirOp::Ret) } } };
    module.funcs.push_back(writer);
    GirFunc reader;
    reader.name = "generic_content_reader";
    reader.params = { holder, slice };
    reader.scopes = { -1 };
    reader.summary.unknown = true;
    reader.roots.params = { { 1, { { CoreRootRef::Param, 1 } } } };
    reader.roots.contents = { { 0, { { CoreRootRef::Param, 1 } } } };
    reader.blocks = { { { { 0, holder }, { 1, slice } }, { Inst(GirOp::Load, 2, 0), Inst(GirOp::SliceView, 3, 2),
        Inst(GirOp::ViewLen, 4, 3), Inst(GirOp::Ret) } } };
    module.funcs.push_back(reader);
    assert(Code(module).empty());
    module.funcs[3].roots.params[0].second.push_back({ CoreRootRef::Global, 1 });
    assert(Code(module).empty());
    module.funcs[3].roots.params[0].second = { { CoreRootRef::Global, 1 }, { CoreRootRef::Global, 2 } };
    assert(Code(module).empty());
    module.funcs[3].roots.params[0].second = { { CoreRootRef::Global, 1 } };
    assert(Code(module) == "GIR-V060");
    module.funcs[3].roots.params.clear();
    assert(Code(module) == "GIR-V060");
}

void ChecksActualHolderAliasesAfterCallWrites() {
    for (bool aliased : { false, true })
        assert(Code(ActualHolderAliasModule(aliased)) == (aliased ? "GIR-V060" : ""));
}

void ChecksInitializerHolderAliasesAfterCallWrites() {
    for (bool aliased : { false, true }) {
        auto module = ActualHolderAliasModule(aliased);
        auto initializer = std::move(module.funcs[0]);
        module.funcs[0] = Module().funcs[0];
        auto integer = module.IntType(CoreIntTy::I64);
        initializer.results = { integer };
        initializer.blocks[0].insts.pop_back();
        auto zero = Inst(GirOp::Int, 8);
        zero.ty = integer;
        zero.text = "0";
        initializer.blocks[0].insts.push_back(zero);
        auto ret = Inst(GirOp::Ret);
        ret.vals = { 8 };
        initializer.blocks[0].insts.push_back(ret);
        GirGlobal global;
        global.name = "initializer_callsite";
        global.ty = integer;
        global.init = std::move(initializer);
        module.globals.push_back(std::move(global));
        assert(Code(module) == (aliased ? "GIR-V060" : ""));
    }
}

void PreservesActualReturnedAliases() {
    auto module = EmptyContentReplacement();
    module.funcs.reserve(3);
    auto slice = module.Type(module.funcs[1].params[0]).elem;
    auto &instructions = module.funcs[1].blocks[0].insts;
    auto clear = instructions[4];
    auto emptyLoad = instructions[5];
    instructions.erase(instructions.begin() + 4, instructions.begin() + 6);
    auto view = Inst(GirOp::Snap, 7, 2);
    auto alias = Inst(GirOp::ViewSlice, 8, 7);
    alias.mut = CoreMut::Const;
    auto call = Inst(GirOp::Call, 9);
    call.idx = 2;
    call.vals = { 8 };
    instructions.insert(instructions.begin() + 4, { emptyLoad, view, alias, call, clear });
    for (auto &inst : instructions)
        if (inst.op == GirOp::SliceView) inst.a = 9;
    GirFunc identity;
    identity.name = "slice_identity";
    identity.params = { slice };
    identity.results = { slice };
    identity.roots.results = { { { CoreRootRef::Param, 0 } } };
    identity.summary.unknown = true;
    identity.scopes = { -1 };
    auto ret = Inst(GirOp::Ret);
    ret.vals = { 0 };
    identity.blocks = { { { { 0, slice } }, { ret } } };
    module.funcs.push_back(identity);
    assert(Code(module) == "GIR-V060");
    for (auto &inst : instructions)
        if (inst.op == GirOp::Call) inst.vals = { 3 };
    assert(Code(module).empty());
    module.funcs[2].roots.results[0].push_back({ CoreRootRef::Param, 0 });
    assert(Code(module).empty());
    assert(module.funcs[2].roots.results[0].size() == 2);
    module.funcs[2].roots.results = { {} };
    assert(Code(module) == "GIR-V050");
}

void IncludesActualRefSliceBackingReads() {
    auto module = LocalEmptyContentReplacement();
    module.funcs.reserve(3);
    module.globals = GlobalEmptyContentReplacement().globals;
    auto reference = module.funcs[1].params[0];
    auto &instructions = module.funcs[1].blocks[0].insts;
    for (auto &inst : instructions)
        if (inst.op == GirOp::Slot && inst.res == 2) { inst.op = GirOp::Global; inst.idx = 0; }
    auto clear = instructions[4];
    instructions.erase(instructions.begin() + 4);
    auto snapshot = Inst(GirOp::Snap, 8, 2);
    auto sliced = Inst(GirOp::ViewSlice, 9, 8);
    sliced.mut = CoreMut::Const;
    auto initialize = find_if(instructions.begin(), instructions.end(), [](const GirInst &inst) {
        return inst.op == GirOp::Init && inst.idx == 2;
    });
    initialize->a = 9;
    instructions.insert(initialize, { snapshot, sliced });
    auto load = find_if(instructions.begin(), instructions.end(), [](const GirInst &inst) { return inst.op == GirOp::Load && inst.res == 8; });
    auto offset = load - instructions.begin();
    instructions.erase(instructions.begin() + offset);
    instructions.insert(instructions.begin() + offset, clear);
    for (auto &inst : instructions)
        if (inst.op == GirOp::SliceView && inst.res == 4) inst.a = 3;
    GirFunc reader;
    reader.name = "read_backing";
    reader.params = { reference };
    reader.scopes = { -1 };
    reader.summary.unknown = true;
    reader.roots.contents = { { 0, { { CoreRootRef::Global, 0 } } } };
    reader.blocks = { { { { 0, reference } }, { Inst(GirOp::Load, 1, 0), Inst(GirOp::SliceView, 2, 1),
        Inst(GirOp::ViewLen, 3, 2), Inst(GirOp::Ret) } } };
    module.funcs.push_back(reader);
    auto call = Inst(GirOp::Call);
    call.idx = 2;
    call.vals = { 7 };
    instructions.insert(instructions.end() - 3, call);
    assert(Code(module) == "GIR-V060");
    module.funcs[2].blocks[0].insts = { Inst(GirOp::Load, 1, 0), Inst(GirOp::Ret) };
    assert(Code(module) == "GIR-V060");
    module.funcs[2].blocks[0].insts = { Inst(GirOp::Load, 1, 0), Inst(GirOp::SliceView, 2, 1), Inst(GirOp::Ret) };
    assert(Code(module) == "GIR-V060");
    module.funcs[2].blocks[0].insts = { Inst(GirOp::Ret) };
    module.funcs[2].roots.contents.clear();
    assert(Code(module).empty());
}

}

int main() {
    AdmitsCallerStorageThroughGenericContentBounds();
    DistinguishesReturnedOwnerAddressesFromReads();
    PreservesActualGlobalCallDependencies();
    RetainsSpecializedGlobalPolicyWithEmptyActualArguments();
    CertifiesRecursiveReferenceReturnBounds();
    IncludesActualRefSliceBackingReads();
    PreservesActualReturnedAliases();
    LowersCrossParameterContentBounds();
    ChecksActualHolderAliasesAfterCallWrites();
    ChecksInitializerHolderAliasesAfterCallWrites();
    AcceptsReplacementAfterKnownEmptyContentRead();
    AcceptsStoresBetweenEmptyParameterContents();
    PreservesKnownEmptyLocalCopies();
    RequiresEveryJoinInputKnownEmpty();
    RetainsNonemptyContentAliases();
    RejectsChangedEmptyParameterContents();
    RejectsGlobalContentChangesFromNoArgumentCalls();
    RejectsGlobalContentChangesWithUnusedEmptyArgument();
    PreservesConservativeCallDependencies();
    CertifiesUnknownMemoryFreeCallGraphs();
    RejectsLocalContentChangesWithUnusedEmptyArgument();
    assert(Code(ContentAliasStore()).empty());
    assert(Code(ParameterContentStore()).empty());
    RequiresRebind(LocalBindingStore(false));
    RequiresRebind(LocalBindingStore(true));
    RequiresRebind(SliceParameterBindingStore());
}
