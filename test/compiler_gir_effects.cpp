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
    callee.roots.contents = { { 0, { { CoreRootRef::Param, 1 } } } };
    callee.roots.results = { { { CoreRootRef::Param, 0 }, { CoreRootRef::Param, 1 } } };
    callee.roots.slots.emplace();
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
            assert(Code(module) == "GIR-V050");
            if (called) {
                module.funcs[2].summary.unknown = false;
                module.funcs[2].summary.writes = { { false, 0 } };
                module.funcs[2].summary.rebinds = { { false, 0 } };
                assert(Code(module) == "GIR-V050");
            }
            module.funcs[1].roots.params[1].second.clear();
            assert(Code(module) == (called || aliased ? "GIR-V050" : ""));
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
    assert(Code(module) == "GIR-V010");
    module.funcs[2].summary.unknown = false;
    module.funcs[2].summary.aborts = true;
    module.funcs[2].summary.reads = { { true, 0 } };
    module.funcs[2].summary.writes = { { true, 1 } };
    assert(Code(module) == "GIR-V010");
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
    assert(Code(module) == "GIR-V010");
    module.funcs[2].summary.unknown = false;
    module.funcs[2].summary.aborts = true;
    module.funcs[2].summary.reads = { { true, 0 } };
    module.funcs[2].summary.writes = { { true, 1 } };
    assert(Code(module) == "GIR-V010");
    module.funcs[2].roots.params[0].second = { { CoreRootRef::Global, 1 } };
    module.funcs[2].summary.writes = { { false, 0 } };
    assert(Code(module) == "GIR-V010");
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
    assert(Code(module) == "GIR-V010");
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
        module.funcs[1].roots.slots = vector<pair<int, vector<CoreRootRef>>> {
            { 2, { { CoreRootRef::Local, 1 } } } };
        if (initialRoots != 0) module.funcs[1].roots.slots->at(0).second.push_back({ CoreRootRef::Param, 1 });
        if (initialRoots == 2) {
            module.globals = GlobalEmptyContentReplacement().globals;
            module.funcs[1].roots.params[1].second = { { CoreRootRef::Global, 0 } };
            module.funcs[2].roots.contents[0].second.push_back({ CoreRootRef::Global, 0 });
            module.funcs[1].roots.slots->at(0).second.push_back({ CoreRootRef::Global, 0 });
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

CoreModule BroadSliceReturnReplacement(bool dependent) {
    CoreModule core;
    core.profile = CoreProfile::Shrink;
    core.files = { "broad-slice-return.goose" };
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Expr };
    auto integer = core.IntType(CoreIntTy::I64);
    CoreType owner;
    owner.kind = CoreType::GrowShrink;
    owner.elem = integer;
    auto ownerType = core.Intern(owner);
    CoreType slice;
    slice.kind = CoreType::Slice;
    slice.mut = CoreMut::Const;
    slice.elem = integer;
    auto sliceType = core.Intern(slice);
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
    main.summary.unknown = true;
    CoreStmt assignment;
    assignment.kind = CoreStmtKind::AssignWhole;
    assignment.org = origin;
    assignment.place = make_unique<CorePlace>();
    assignment.place->kind = CorePlace::Global;
    assignment.expr = make_unique<CoreExpr>();
    assignment.expr->kind = CoreExprKind::Arr;
    assignment.expr->type = ownerType;
    auto length = make_unique<CoreExpr>();
    length->kind = CoreExprKind::Len;
    length->org = origin;
    length->view = make_unique<CoreView>();
    length->view->kind = CoreView::Val;
    length->view->expr = make_unique<CoreExpr>();
    length->view->expr->kind = CoreExprKind::Call;
    length->view->expr->ctx = 1;
    length->view->expr->org = origin;
    assignment.expr->elems.push_back(std::move(length));
    main.body.stmts.push_back(std::move(assignment));
    core.impls.push_back(std::move(main));
    CoreContext mainContext;
    mainContext.impl = 0;
    core.contexts.push_back(std::move(mainContext));
    CoreImpl callee;
    callee.name = "broad_slice_return";
    callee.results = { { sliceType } };
    callee.summary.reads = { { true, dependent ? 0 : 1 } };
    callee.summary.aborts = true;
    callee.summary.outputs = true;
    callee.body.value = make_unique<CoreExpr>();
    callee.body.value->kind = CoreExprKind::Slice;
    callee.body.value->mut = CoreMut::Const;
    callee.body.value->org = origin;
    callee.body.value->view = make_unique<CoreView>();
    callee.body.value->view->place = make_unique<CorePlace>();
    callee.body.value->view->place->kind = CorePlace::Global;
    callee.body.value->view->place->index = dependent ? 0 : 1;
    core.impls.push_back(std::move(callee));
    CoreContext calleeContext;
    calleeContext.impl = 1;
    calleeContext.resultroots = { { { CoreRootRef::Global, 0 }, { CoreRootRef::Global, 1 } } };
    core.contexts.push_back(std::move(calleeContext));
    return core;
}

void PreservesLeastActualReturnRoots() {
    auto lower = [](bool dependent) {
        auto core = BroadSliceReturnReplacement(dependent);
        return GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Expr } },
            [](const CoreOrigin &) { return 0; }).Lower();
    };
    for (bool dependent : { false, true }) {
        auto observed = Code(lower(dependent));
        auto expected = dependent ? "GIR-V060" : "";
        if (observed != expected) fprintf(stderr, "broad return dependent=%d: %s\n", dependent, observed.c_str());
        assert(observed == expected);
    }
    auto module = lower(true);
    auto &instructions = module.funcs[0].blocks[0].insts;
    auto position = find_if(instructions.begin(), instructions.end(), [](const GirInst &inst) { return inst.op == GirOp::Call; });
    auto delayedReturn = *position;
    instructions.erase(position);
    position = find_if(instructions.begin(), instructions.end(), [](const GirInst &inst) { return inst.op == GirOp::Clear; });
    instructions.insert(position, delayedReturn);
    assert(Code(module) == "GIR-V060");
    module = lower(false);
    auto &callee = module.funcs[1];
    auto slice = callee.results[0];
    auto recursive = Inst(GirOp::Call, 0);
    recursive.idx = 1;
    auto ret = Inst(GirOp::Ret);
    ret.vals = { 0 };
    callee.summary.unknown = true;
    callee.blocks = { { {}, { recursive, ret } } };
    assert(Code(module).empty());
    auto condition = Inst(GirOp::Bool, 0);
    condition.flag = true;
    auto branch = Inst(GirOp::CondBr, -1, 0);
    branch.idx = 1;
    branch.idx2 = 2;
    recursive.res = 1;
    ret.vals = { 1 };
    auto global = Inst(GirOp::Global, 2);
    global.idx = 1;
    auto returned = Inst(GirOp::ViewSlice, 4, 3);
    returned.mut = CoreMut::Const;
    auto baseRet = Inst(GirOp::Ret);
    baseRet.vals = { 4 };
    callee.blocks = { { {}, { condition, branch } }, { {}, { recursive, ret } },
        { {}, { global, Inst(GirOp::Snap, 3, 2), returned, baseRet } } };
    assert(Code(module).empty());
    callee.blocks[2].insts[0].idx = 0;
    assert(Code(module) == "GIR-V060");
    callee.blocks[2].insts[0].idx = 1;
    auto anotherBase = callee.blocks[2];
    anotherBase.insts[0].res = 6;
    anotherBase.insts[0].idx = 0;
    anotherBase.insts[1] = Inst(GirOp::Snap, 7, 6);
    anotherBase.insts[2].res = 8;
    anotherBase.insts[2].a = 7;
    anotherBase.insts[3].vals = { 8 };
    auto otherCondition = Inst(GirOp::Bool, 5);
    auto otherBranch = Inst(GirOp::CondBr, -1, 5);
    otherBranch.idx = 2;
    otherBranch.idx2 = 4;
    callee.blocks[0].insts[1].idx2 = 3;
    callee.blocks.push_back({ {}, { otherCondition, otherBranch } });
    callee.blocks.push_back(std::move(anotherBase));
    assert(Code(module) == "GIR-V060");
    module = lower(false);
    GirFunc forwarder;
    forwarder.name = "return_forwarder";
    forwarder.results = { slice };
    forwarder.roots.results = module.funcs[1].roots.results;
    forwarder.roots.slots.emplace();
    forwarder.scopes = { -1 };
    forwarder.summary.unknown = true;
    auto call = Inst(GirOp::Call, 0);
    call.idx = 1;
    ret.vals = { 0 };
    forwarder.blocks = { { {}, { call, ret } } };
    module.funcs.push_back(forwarder);
    for (auto &inst : module.funcs[0].blocks[0].insts)
        if (inst.op == GirOp::Call) inst.idx = 2;
    assert(Code(module).empty());
    GirGlobal initializer;
    initializer.name = "returned_length";
    initializer.ty = module.IntType(CoreIntTy::I64);
    initializer.kind = CoreVarKind::Let;
    initializer.init.name = "returned_length_init";
    initializer.init.results = { initializer.ty };
    initializer.init.scopes = { -1 };
    initializer.init.summary.unknown = true;
    global = Inst(GirOp::Global, 0);
    global.idx = 0;
    call.res = 1;
    call.idx = 2;
    auto array = Inst(GirOp::Arr, 4);
    array.ty = module.globals[0].ty;
    array.vals = { 3 };
    auto zero = Inst(GirOp::Int, 5);
    zero.ty = initializer.ty;
    zero.text = "0";
    ret.vals = { 5 };
    initializer.init.blocks = { { {}, { global, Inst(GirOp::Clear, -1, 0), call,
        Inst(GirOp::SliceView, 2, 1), Inst(GirOp::ViewLen, 3, 2), array,
        Inst(GirOp::Replace, -1, 0, 4), zero, ret } } };
    module.globals.push_back(std::move(initializer));
    module.funcs[0] = Module().funcs[0];
    assert(Code(module).empty());
    auto &body = module.funcs[1].blocks[0].insts;
    auto actualGlobal = find_if(body.begin(), body.end(), [](const GirInst &inst) { return inst.op == GirOp::Global; });
    actualGlobal->idx = 0;
    module.funcs[1].summary.reads = { { true, 0 } };
    assert(Code(module) == "GIR-V060");
    actualGlobal->idx = 1;
    module.funcs[1].summary.reads = { { true, 1 } };
    module.funcs[1].roots.results = { { { CoreRootRef::Global, 0 } } };
    assert(Code(module) == "GIR-V050");
}

void PreservesOptionalSlotRootMetadata() {
    auto raw = Module();
    auto oldWire = GirWriter(raw).Write();
    assert(oldWire.find("[\"roots\",[],[],[]]") != string::npos);
    raw.funcs[0].roots.slots.emplace();
    auto sourceWire = GirWriter(raw).Write();
    assert(sourceWire.find("[\"roots\",[],[],[],[]]") != string::npos);
    raw.funcs[0].roots.slots.reset();
    assert(GirWriter(raw).Write() == oldWire);
    auto core = OwnerReferenceReplacement(false, OwnerReferenceUse::Unused, OwnerReferenceForm::LocalCopyCall);
    auto gir = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Expr } },
        [](const CoreOrigin &) { return 0; }).Lower();
    vector<pair<int, vector<CoreRootRef>>> expected { { 0, { { CoreRootRef::Global, 1 } } } };
    assert(gir.funcs[0].roots.slots == expected);
    assert(gir.funcs[1].roots.slots == expected);
    assert(GirWriter(gir).Write().find("[\"sr\",0,[[\"r_global\",1]]]") != string::npos);
    core = OwnerReferenceReplacement(false, OwnerReferenceUse::Unused);
    gir = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Expr } },
        [](const CoreOrigin &) { return 0; }).Lower();
    assert(gir.funcs[1].roots.slots && gir.funcs[1].roots.slots->empty());
    assert(Code(gir).empty());
    auto low = GirToLow(gir).Lower();
    assert(Code(low).empty());
    for (auto &function : low.funcs) assert(!function.roots.slots);
    assert(gir.funcs[0].roots.slots && !gir.funcs[0].roots.slots->empty());
}

void PreservesOptionalValueRootMetadata() {
    auto raw = Module();
    auto oldWire = GirWriter(raw).Write();
    raw.funcs[0].roots.values.emplace();
    auto noSlots = GirWriter(raw).Write();
    assert(noSlots.find("[\"roots\",[],[],[],null,[]]") != string::npos);
    raw.funcs[0].roots.slots.emplace();
    auto emptySlots = GirWriter(raw).Write();
    assert(emptySlots.find("[\"roots\",[],[],[],[],[]]") != string::npos);
    raw.funcs[0].roots.values->push_back({ 3, { { CoreRootRef::Global, 1 } } });
    assert(GirWriter(raw).Write().find("[\"er\",3,[[\"r_global\",1]]]") != string::npos);
    raw.funcs[0].roots.values.reset();
    assert(GirWriter(raw).Write().find("[\"roots\",[],[],[],[]]") != string::npos);
    raw.funcs[0].roots.slots.reset();
    assert(GirWriter(raw).Write() == oldWire);
}

void EnforcesSourceValueRootCeilings() {
    auto module = Module();
    auto integer = module.IntType(CoreIntTy::I64);
    module.funcs[0].slots = { { integer, CoreVarKind::Var, 0, 0 } };
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto address = Inst(GirOp::Slot, 0);
    address.idx = 0;
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    module.funcs[0].blocks = { { {}, { enter, address, Inst(GirOp::Freeze, 1, 0),
        Inst(GirOp::Load, 2, 1), leave, Inst(GirOp::Ret) } } };
    module.funcs[0].roots.values = vector<pair<int, vector<CoreRootRef>>> {
        { 1, { { CoreRootRef::Local, 0 } } }
    };
    assert(Code(module).empty());
    module.funcs[0].roots.values->at(0).second.clear();
    assert(Code(module) == "GIR-V050");
    module.funcs[0].roots.values = vector<pair<int, vector<CoreRootRef>>> {
        { 1, { { CoreRootRef::Local, 0 } } }, { 1, {} }
    };
    assert(Code(module) == "GIR-V001");
    module.funcs[0].roots.values = vector<pair<int, vector<CoreRootRef>>> { { 2, {} } };
    assert(Code(module) == "GIR-V010");
    module.funcs[0].roots.values = vector<pair<int, vector<CoreRootRef>>> { { 3, {} } };
    assert(Code(module) == "GIR-V001");
}

void RejectsWideValueRootsAtNarrowSlots() {
    auto module = Module();
    auto integer = module.IntType(CoreIntTy::I64);
    auto reference = module.RefType(CoreMut::Const, integer);
    for (auto name : { "first", "second" }) {
        GirGlobal global;
        global.name = name;
        global.ty = integer;
        global.kind = CoreVarKind::Var;
        global.init.name = cat(name, "_init");
        global.init.results = { integer };
        global.init.scopes = { -1 };
        auto zero = Inst(GirOp::Int, 0);
        zero.ty = integer;
        zero.text = "0";
        auto ret = Inst(GirOp::Ret);
        ret.vals = { 0 };
        global.init.blocks = { { {}, { zero, ret } } };
        module.globals.push_back(std::move(global));
    }
    auto &function = module.funcs[0];
    function.slots = { { reference, CoreVarKind::Var, 0, 0 } };
    function.roots.slots = vector<pair<int, vector<CoreRootRef>>> {
        { 0, { { CoreRootRef::Global, 0 } } }
    };
    function.roots.values = vector<pair<int, vector<CoreRootRef>>> {
        { 2, { { CoreRootRef::Global, 0 }, { CoreRootRef::Global, 1 } } }
    };
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto address = Inst(GirOp::Slot, 0);
    address.idx = 0;
    auto global = Inst(GirOp::Global, 1);
    global.idx = 0;
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    function.blocks = { { {}, { enter, address, global, Inst(GirOp::Freeze, 2, 1),
        Inst(GirOp::Store, -1, 0, 2), leave, Inst(GirOp::Ret) } } };
    assert(Code(module) == "GIR-V050");
}

void LowersStoppedConditionalRootsPerContext() {
    CoreModule core;
    core.files = { "conditional-source-roots.goose" };
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Expr };
    auto integer = core.IntType(CoreIntTy::I64);
    auto boolean = core.BoolType();
    CoreType reference;
    reference.kind = CoreType::Ref;
    reference.mut = CoreMut::Const;
    reference.elem = integer;
    auto referenceType = core.Intern(reference);
    for (int index = 0; index < 3; index++) {
        CoreGlobal global;
        global.name = cat("root", index);
        global.type = integer;
        global.org = origin;
        global.init = make_unique<CoreExpr>();
        global.init->kind = CoreExprKind::Lit;
        global.init->type = integer;
        global.init->value = "0";
        core.globals.push_back(std::move(global));
    }
    CoreImpl entry;
    entry.name = "main";
    entry.body.scope = 0;
    core.impls.push_back(std::move(entry));
    CoreContext entryContext;
    entryContext.impl = 0;
    core.contexts.push_back(std::move(entryContext));
    CoreImpl function;
    function.name = "conditional";
    function.params = { { 0, true } };
    function.vars = { { "source", referenceType, CoreVarKind::Let, 0, origin } };
    function.results = { { referenceType, CoreRequest::Register, nullopt } };
    function.summary.aborts = true;
    function.body.scope = 0;
    function.body.value = make_unique<CoreExpr>();
    function.body.value->kind = CoreExprKind::If;
    function.body.value->type = referenceType;
    function.body.value->org = origin;
    function.body.value->a = make_unique<CoreExpr>();
    function.body.value->a->kind = CoreExprKind::Bool;
    function.body.value->a->type = boolean;
    function.body.value->a->flag = true;
    function.body.value->then = make_unique<CoreBlock>();
    function.body.value->then->scope = 1;
    CoreStmt abort;
    abort.kind = CoreStmtKind::Abort;
    abort.org = origin;
    function.body.value->then->stmts.push_back(std::move(abort));
    function.body.value->then->value = make_unique<CoreExpr>();
    function.body.value->then->value->kind = CoreExprKind::Read;
    function.body.value->then->value->type = referenceType;
    function.body.value->then->value->place = make_unique<CorePlace>();
    function.body.value->then->value->place->kind = CorePlace::Local;
    function.body.value->then->value->place->index = 0;
    function.body.value->otherwise = make_unique<CoreBlock>();
    function.body.value->otherwise->scope = 2;
    function.body.value->otherwise->value = make_unique<CoreExpr>();
    function.body.value->otherwise->value->kind = CoreExprKind::Ref;
    function.body.value->otherwise->value->type = referenceType;
    function.body.value->otherwise->value->mut = CoreMut::Const;
    function.body.value->otherwise->value->place = make_unique<CorePlace>();
    function.body.value->otherwise->value->place->kind = CorePlace::Global;
    function.body.value->otherwise->value->place->index = 0;
    core.impls.push_back(std::move(function));
    for (int root : { 1, 2 }) {
        CoreContext context;
        context.impl = 1;
        context.varroots = { { 0, { { CoreRootRef::Global, root } } } };
        context.resultroots = { { { CoreRootRef::Global, 0 }, { CoreRootRef::Global, root } } };
        core.contexts.push_back(std::move(context));
    }
    auto gir = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
    assert(gir.funcs[1].roots.values && gir.funcs[1].roots.values->size() == 1);
    assert(gir.funcs[2].roots.values && gir.funcs[2].roots.values->size() == 1);
    auto first = gir.funcs[1].roots.values->front().second;
    auto second = gir.funcs[2].roots.values->front().second;
    assert(find(first.begin(), first.end(), CoreRootRef { CoreRootRef::Global, 0 }) != first.end());
    assert(find(first.begin(), first.end(), CoreRootRef { CoreRootRef::Global, 1 }) != first.end());
    assert(find(second.begin(), second.end(), CoreRootRef { CoreRootRef::Global, 0 }) != second.end());
    assert(find(second.begin(), second.end(), CoreRootRef { CoreRootRef::Global, 2 }) != second.end());
    assert(first != second);
    assert(Code(gir).empty());
}

void EnforcesDeclaredRegionCeilings() {
    auto lower = [](CoreModule core) {
        return GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Expr } },
            [](const CoreOrigin &) { return 0; }).Lower();
    };
    auto module = lower(OwnerReferenceReplacement(false, OwnerReferenceUse::Unused, OwnerReferenceForm::LocalCopyCall));
    assert(Code(module).empty());
    module.funcs[0].roots.slots->at(0).second = { { CoreRootRef::Global, 0 } };
    assert(Code(module) == "GIR-V050");
    module = lower(OwnerReferenceReplacement(false, OwnerReferenceUse::Unused));
    module.funcs[0].roots.slots->push_back(module.funcs[0].roots.slots->at(0));
    assert(Code(module) == "GIR-V001");
    module = lower(OwnerReferenceReplacement(false, OwnerReferenceUse::Length));
    module.funcs[1].roots.results[0].push_back({ CoreRootRef::Global, 0 });
    auto call = Inst(GirOp::Call, 0);
    call.idx = 1;
    auto &entry = module.funcs[0];
    entry.slots.clear();
    entry.roots.slots->clear();
    entry.summary = {};
    entry.summary.reads = { { true, 1 } };
    entry.blocks = { { {}, { call, Inst(GirOp::Snap, 1, 0), Inst(GirOp::ViewLen, 2, 1), Inst(GirOp::Ret) } } };
    assert(Code(module) == "GIR-V050");
    for (auto &function : module.funcs) function.roots.slots.reset();
    assert(Code(module).empty());
    module = GlobalEmptyContentReplacement();
    module.funcs = Module().funcs;
    auto reference = module.RefType(CoreMut::Const, module.globals[0].ty);
    GirGlobal referenceGlobal;
    referenceGlobal.name = "reference_global";
    referenceGlobal.ty = reference;
    referenceGlobal.init.name = "reference_global_init";
    referenceGlobal.init.results = { reference };
    referenceGlobal.init.scopes = { -1 };
    referenceGlobal.init.roots.results = { { { CoreRootRef::Global, 0 } } };
    auto globalAddress = Inst(GirOp::Global, 0);
    globalAddress.idx = 0;
    auto ret = Inst(GirOp::Ret);
    ret.vals = { 1 };
    referenceGlobal.init.blocks = { { {}, { globalAddress, Inst(GirOp::Freeze, 1, 0), ret } } };
    module.globals.push_back(std::move(referenceGlobal));
    assert(Code(module) == "GIR-V010");
    module.funcs[0].roots.slots.emplace();
    assert(Code(module) == "GIR-V010");
    module.types[reference].elem = -1;
    assert(Code(module) == "GIR-V010");
    module = GlobalEmptyContentReplacement();
    module.funcs = Module().funcs;
    auto second = module.globals[0];
    second.name = "second_owner";
    module.globals.push_back(std::move(second));
    auto owner = module.globals[0].ty;
    auto &initializer = module.globals[1].init;
    initializer.slots = { { module.RefType(CoreMut::Mut, owner), CoreVarKind::Let, 0, 0 } };
    initializer.roots.slots = vector<pair<int, vector<CoreRootRef>>> { { 0, { { CoreRootRef::Global, 1 } } } };
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto initialize = Inst(GirOp::Init, -1, 0);
    initialize.idx = 0;
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    auto empty = Inst(GirOp::Arr, 1);
    empty.ty = owner;
    initializer.blocks = { { {}, { enter, globalAddress, initialize, leave, empty, ret } } };
    assert(Code(module) == "GIR-V050");
    initializer.roots.slots->at(0).second = { { CoreRootRef::Global, 0 } };
    assert(Code(module).empty());
}

CoreModule WidenedLocalContentRegion() {
    CoreModule core;
    core.profile = CoreProfile::Pilot;
    core.files = { "widened-local-content.goose" };
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Call };
    auto boolean = core.BoolType();
    CoreType slice;
    slice.kind = CoreType::Slice;
    slice.mut = CoreMut::Mut;
    slice.elem = boolean;
    auto sliceType = core.Intern(slice);
    CoreType holder;
    holder.kind = CoreType::Ref;
    holder.mut = CoreMut::Mut;
    holder.elem = sliceType;
    auto holderType = core.Intern(holder);
    CoreImpl main;
    main.name = "main";
    main.summary.unknown = true;
    core.impls.push_back(std::move(main));
    CoreContext mainContext;
    mainContext.impl = 0;
    core.contexts.push_back(std::move(mainContext));
    auto read = [](int variable) {
        auto expression = make_unique<CoreExpr>();
        expression->kind = CoreExprKind::Read;
        expression->place = make_unique<CorePlace>();
        expression->place->index = variable;
        return expression;
    };
    CoreImpl wrapper;
    wrapper.name = "wrapper";
    wrapper.params = { { 0, true }, { 1, false }, { 2, false } };
    wrapper.vars = { { "holder", holderType, CoreVarKind::Let, 0, origin },
        { "a", sliceType, CoreVarKind::Let, 0, origin }, { "b", sliceType, CoreVarKind::Let, 0, origin },
        { "wide", sliceType, CoreVarKind::Let, 0, origin } };
    wrapper.summary.unknown = true;
    CoreStmt bind;
    bind.kind = CoreStmtKind::Let;
    bind.var = 3;
    bind.org = origin;
    bind.expr = read(1);
    wrapper.body.stmts.push_back(std::move(bind));
    CoreStmt call;
    call.kind = CoreStmtKind::Expr;
    call.org = origin;
    call.expr = make_unique<CoreExpr>();
    call.expr->kind = CoreExprKind::Call;
    call.expr->ctx = 2;
    call.expr->org = origin;
    auto place = make_unique<CorePlace>();
    place->kind = CorePlace::Deref;
    place->expr = read(0);
    call.expr->args.push_back(CoreArgReference { CoreMut::Mut, std::move(place) });
    call.expr->args.push_back(CoreArgValue { read(3) });
    wrapper.body.stmts.push_back(std::move(call));
    core.impls.push_back(std::move(wrapper));
    CoreContext wrapperContext;
    wrapperContext.impl = 1;
    wrapperContext.varroots = { { 0, { { CoreRootRef::Param, 0 } } }, { 1, { { CoreRootRef::Param, 1 } } },
        { 2, { { CoreRootRef::Param, 2 } } }, { 3, { { CoreRootRef::Param, 1 }, { CoreRootRef::Param, 2 } } } };
    wrapperContext.content = { { { CoreRootRef::Param, 1 }, { CoreRootRef::Param, 2 } }, {}, {}, {} };
    wrapperContext.hascontent = { 1, 0, 0, 0 };
    core.contexts.push_back(std::move(wrapperContext));
    CoreImpl callee;
    callee.name = "callee";
    callee.params = { { 0, true }, { 1, false } };
    callee.vars = { { "holder", holderType, CoreVarKind::Let, 0, origin }, { "value", sliceType, CoreVarKind::Let, 0, origin } };
    callee.summary.unknown = true;
    core.impls.push_back(std::move(callee));
    CoreContext calleeContext;
    calleeContext.impl = 2;
    calleeContext.varroots = { { 0, { { CoreRootRef::Param, 0 } } }, { 1, { { CoreRootRef::Param, 1 } } } };
    calleeContext.content = { { { CoreRootRef::Param, 1 } }, {} };
    calleeContext.hascontent = { 1, 0 };
    core.contexts.push_back(std::move(calleeContext));
    return core;
}

CoreModule SpecializedForwardContentRegion() {
    auto core = WidenedLocalContentRegion();
    auto boolean = core.BoolType();
    CoreType array;
    array.kind = CoreType::Arr;
    array.elem = boolean;
    array.count = 1;
    auto arrayType = core.Intern(array);
    CoreGlobal global;
    global.name = "backing";
    global.type = arrayType;
    global.kind = CoreVarKind::Var;
    global.org = { 0, 1, CoreOriginKind::Let };
    global.init = make_unique<CoreExpr>();
    global.init->kind = CoreExprKind::Arr;
    global.init->type = arrayType;
    global.init->elems.push_back(make_unique<CoreExpr>());
    core.globals.push_back(std::move(global));
    for (int variable : { 1, 2, 3 }) core.contexts[1].varroots[variable].second = { { CoreRootRef::Global, 0 } };
    core.contexts[1].content[0] = { { CoreRootRef::Global, 0 } };
    core.contexts[2].varroots[1].second = { { CoreRootRef::Global, 0 } };
    return core;
}

void NormalizesSpecializedForwardContentRegions() {
    auto core = SpecializedForwardContentRegion();
    auto gir = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Call } },
        [](const CoreOrigin &) { return 0; }).Lower();
    assert(Code(gir).empty());
    gir.funcs[2].roots.contents[0].second.clear();
    assert(Code(gir) == "GIR-V050");
}

void PreservesWidenedSourceLocalContentRegions() {
    auto core = WidenedLocalContentRegion();
    auto gir = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Call } },
        [](const CoreOrigin &) { return 0; }).Lower();
    assert(Code(gir).empty());
    auto low = GirToLow(gir).Lower();
    assert(Code(low).empty());
    for (auto &function : low.funcs) assert(!function.roots.slots);
    for (auto &function : gir.funcs) function.roots.slots.reset();
    assert(Code(gir) == "GIR-V050");
    core.impls[1].vars[3].type = core.impls[1].vars[0].type;
    core.impls[1].body.stmts.clear();
    auto malformed = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Call } },
        [](const CoreOrigin &) { return 0; }).Lower();
    assert(Code(malformed) == "GIR-V010");
}

CoreModule MixedSelfArgumentRegion() {
    CoreModule core;
    core.files = { "mixed-self-content.goose" };
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Call };
    auto integer = core.IntType(CoreIntTy::I64);
    auto boolean = core.BoolType();
    CoreType slice;
    slice.kind = CoreType::Slice;
    slice.mut = CoreMut::Mut;
    slice.elem = integer;
    auto sliceType = core.Intern(slice);
    CoreType holder;
    holder.kind = CoreType::Ref;
    holder.mut = CoreMut::Mut;
    holder.elem = sliceType;
    auto holderType = core.Intern(holder);
    CoreType reference;
    reference.kind = CoreType::Ref;
    reference.mut = CoreMut::Const;
    reference.elem = integer;
    auto referenceType = core.Intern(reference);
    for (auto name : { "first", "second" }) {
        CoreGlobal global;
        global.name = name;
        global.type = integer;
        global.kind = CoreVarKind::Var;
        global.org = origin;
        global.init = make_unique<CoreExpr>();
        global.init->kind = CoreExprKind::Lit;
        global.init->type = integer;
        global.init->value = "0";
        core.globals.push_back(std::move(global));
    }
    CoreImpl main;
    main.name = "main";
    core.impls.push_back(std::move(main));
    CoreContext entry;
    entry.impl = 0;
    core.contexts.push_back(std::move(entry));
    CoreImpl caller;
    caller.name = "caller";
    caller.params = { { 0, true }, { 1, true } };
    caller.vars = { { "holder", holderType, CoreVarKind::Let, 0, origin },
        { "root", referenceType, CoreVarKind::Let, 0, origin } };
    caller.summary.unknown = true;
    CoreStmt call;
    call.kind = CoreStmtKind::Expr;
    call.org = origin;
    call.expr = make_unique<CoreExpr>();
    call.expr->kind = CoreExprKind::Call;
    call.expr->ctx = 2;
    call.expr->org = origin;
    auto truth = make_unique<CoreExpr>();
    truth->kind = CoreExprKind::Bool;
    truth->flag = true;
    call.expr->args.push_back(CoreArgValue { std::move(truth) });
    auto payload = make_unique<CoreExpr>();
    payload->kind = CoreExprKind::Read;
    payload->place = make_unique<CorePlace>();
    payload->place->kind = CorePlace::Deref;
    payload->place->expr = make_unique<CoreExpr>();
    payload->place->expr->kind = CoreExprKind::Read;
    payload->place->expr->place = make_unique<CorePlace>();
    call.expr->args.push_back(CoreArgValue { std::move(payload) });
    caller.body.stmts.push_back(std::move(call));
    core.impls.push_back(std::move(caller));
    CoreContext callerContext;
    callerContext.impl = 1;
    callerContext.varroots = { { 0, { { CoreRootRef::Param, 0 } } },
        { 1, { { CoreRootRef::Param, 1 }, { CoreRootRef::Global, 0 } } } };
    callerContext.content = { { { CoreRootRef::Param, 1 } }, {} };
    callerContext.hascontent = { 1, 0 };
    core.contexts.push_back(std::move(callerContext));
    CoreImpl callee;
    callee.name = "callee";
    callee.params = { { 0, false }, { 1, false } };
    callee.vars = { { "unused", boolean, CoreVarKind::Let, 0, origin },
        { "slice", sliceType, CoreVarKind::Let, 0, origin } };
    core.impls.push_back(std::move(callee));
    CoreContext calleeContext;
    calleeContext.impl = 2;
    calleeContext.varroots = { { 1, { { CoreRootRef::Param, 1 }, { CoreRootRef::Global, 1 } } } };
    core.contexts.push_back(std::move(calleeContext));
    return core;
}

void AdmitsMixedSelfSourceArgumentRegions() {
    auto core = MixedSelfArgumentRegion();
    auto gir = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Call } },
        [](const CoreOrigin &) { return 0; }).Lower();
    assert(Code(gir).empty());
    gir.funcs[2].roots.params[0].second = { { CoreRootRef::Global, 1 } };
    assert(Code(gir) == "GIR-V050");
}

void ChecksEveryPossibleContentReceiver() {
    auto module = GlobalEmptyContentReplacement();
    auto other = module.globals[0];
    other.name = "other";
    module.globals.push_back(std::move(other));
    auto integer = module.Type(module.globals[0].ty).elem;
    auto slice = module.SliceType(CoreMut::Mut, integer);
    auto holder = module.RefType(CoreMut::Mut, slice);
    module.funcs.clear();
    GirFunc caller;
    caller.name = "phi_receiver";
    caller.scopes = { -1 };
    caller.slots = { { slice, CoreVarKind::Var, 0, 0 }, { slice, CoreVarKind::Var, 0, 1 } };
    caller.roots.slots = vector<pair<int, vector<CoreRootRef>>> {
        { 0, { { CoreRootRef::Global, 0 } } }, { 1, { { CoreRootRef::Global, 1 } } } };
    caller.summary.reads = { { true, 0 }, { true, 1 } };
    caller.summary.writes = { { true, 0 } };
    caller.summary.aborts = true;
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto first = Inst(GirOp::Global, 0);
    first.idx = 0;
    auto second = Inst(GirOp::Global, 3);
    second.idx = 1;
    auto initial = Inst(GirOp::ViewSlice, 2, 1);
    initial.mut = CoreMut::Mut;
    auto payload = Inst(GirOp::ViewSlice, 5, 4);
    payload.mut = CoreMut::Mut;
    auto initializeFirst = Inst(GirOp::Init, -1, 2);
    initializeFirst.idx = 0;
    auto initializeSecond = Inst(GirOp::Init, -1, 5);
    initializeSecond.idx = 1;
    auto firstSlot = Inst(GirOp::Slot, 6);
    firstSlot.idx = 0;
    auto secondSlot = Inst(GirOp::Slot, 7);
    secondSlot.idx = 1;
    auto condition = Inst(GirOp::Bool, 8);
    condition.flag = true;
    auto branch = Inst(GirOp::CondBr, -1, 8);
    branch.idx = branch.idx2 = 1;
    branch.vals = { 6 };
    branch.vals2 = { 7 };
    auto call = Inst(GirOp::Call);
    call.idx = 1;
    call.vals = { 9 };
    auto address = Inst(GirOp::Slot, 10);
    address.idx = 0;
    auto zero = Inst(GirOp::Int, 13);
    zero.ty = integer;
    zero.text = "0";
    auto value = Inst(GirOp::Int, 15);
    value.ty = integer;
    value.text = "7";
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    caller.blocks = { { {}, { enter, first, Inst(GirOp::Snap, 1, 0), initial, initializeFirst,
        second, Inst(GirOp::Snap, 4, 3), payload, initializeSecond, firstSlot, secondSlot, condition, branch } },
        { { { 9, holder } }, { call, address, Inst(GirOp::Load, 11, 10), Inst(GirOp::SliceView, 12, 11), zero,
            Inst(GirOp::Index, 14, 12, 13), value, Inst(GirOp::Store, -1, 14, 15), leave, Inst(GirOp::Ret) } } };
    module.funcs.push_back(caller);
    GirFunc callee;
    callee.name = "phi_writer";
    callee.params = { holder };
    callee.scopes = { -1 };
    callee.roots.contents = { { 0, { { CoreRootRef::Global, 0 }, { CoreRootRef::Global, 1 } } } };
    callee.roots.slots.emplace();
    callee.summary.reads = { { true, 1 } };
    callee.summary.writes = { { false, 0 } };
    callee.summary.rebinds = { { false, 0 } };
    callee.summary.aborts = true;
    auto source = Inst(GirOp::Global, 1);
    source.idx = 1;
    auto stored = Inst(GirOp::ViewSlice, 3, 2);
    stored.mut = CoreMut::Mut;
    callee.blocks = { { { { 0, holder } }, { source, Inst(GirOp::Snap, 2, 1), stored,
        Inst(GirOp::Store, -1, 0, 3), Inst(GirOp::Ret) } } };
    module.funcs.push_back(callee);
    assert(Code(module) == "GIR-V050");
    for (auto &row : *module.funcs[0].roots.slots)
        row.second = { { CoreRootRef::Global, 0 }, { CoreRootRef::Global, 1 } };
    module.funcs[0].summary.writes.push_back({ true, 1 });
    assert(Code(module).empty());
}

void NormalizesRawSpecializedCallContentRegions() {
    auto module = GlobalEmptyContentReplacement();
    auto holder = module.funcs[1].params[0];
    auto slice = module.Type(holder).elem;
    module.funcs = Module().funcs;
    GirFunc wrapper;
    wrapper.name = "raw_specialized_wrapper";
    wrapper.params = { holder, slice };
    wrapper.scopes = { -1 };
    wrapper.summary.unknown = true;
    wrapper.roots.params = { { 1, { { CoreRootRef::Global, 0 } } } };
    wrapper.roots.contents = { { 0, { { CoreRootRef::Global, 0 } } } };
    auto call = Inst(GirOp::Call);
    call.idx = 2;
    call.vals = { 0, 1 };
    wrapper.blocks = { { { { 0, holder }, { 1, slice } }, { call, Inst(GirOp::Ret) } } };
    module.funcs.push_back(wrapper);
    GirFunc callee;
    callee.name = "raw_specialized_callee";
    callee.params = { holder, slice };
    callee.scopes = { -1 };
    callee.roots.contents = { { 0, { { CoreRootRef::Param, 1 } } } };
    callee.blocks = { { { { 0, holder }, { 1, slice } }, { Inst(GirOp::Ret) } } };
    module.funcs.push_back(callee);
    assert(Code(module) == "GIR-V050");
    module.funcs[1].params.push_back(slice);
    module.funcs[1].blocks[0].params.push_back({ 2, slice });
    module.funcs[1].roots.params.push_back({ 2, { { CoreRootRef::Global, 0 } } });
    module.funcs[1].roots.contents[0].second = { { CoreRootRef::Param, 2 }, { CoreRootRef::Global, 0 } };
    module.funcs[2].roots.contents[0].second.push_back({ CoreRootRef::Global, 0 });
    assert(Code(module).empty());
    module.funcs[2].roots.contents[0].second.clear();
    assert(Code(module) == "GIR-V050");
}

void ChecksConstructingCallContentRegions() {
    for (auto opcode : { GirOp::CallConstruct, GirOp::Invoke }) {
        auto module = Module();
        module.profile = CoreProfile::Construction;
        auto integer = module.IntType(CoreIntTy::I64);
        CoreType owner;
        owner.kind = CoreType::Grow;
        owner.elem = integer;
        auto ownerType = module.Intern(owner);
        auto slice = module.SliceType(CoreMut::Mut, integer);
        auto holder = module.RefType(CoreMut::Mut, slice);
        auto destination = module.CarrierType(CoreType::Dest, ownerType, CoreRequest::Value);
        auto built = module.CarrierType(CoreType::Built, ownerType, CoreRequest::Value);
        GirFunc caller;
        caller.name = "constructing_region_caller";
        caller.params = { slice, slice };
        caller.slots = { { slice, CoreVarKind::Var, 0, 0 }, { ownerType, CoreVarKind::Let, 0, 1 } };
        caller.scopes = { -1 };
        caller.summary.unknown = true;
        caller.roots.slots = vector<pair<int, vector<CoreRootRef>>> { { 0, { { CoreRootRef::Param, 0 } } } };
        auto enter = Inst(GirOp::Enter);
        enter.idx = 0;
        auto initialize = Inst(GirOp::Init, -1, 0);
        initialize.idx = 0;
        auto address = Inst(GirOp::Slot, 2);
        address.idx = 0;
        auto count = Inst(GirOp::Int, 3);
        count.ty = integer;
        count.text = "1";
        auto open = Inst(GirOp::DestOpen, 4);
        open.destReceiver = GirDestSlotReceiver { 1 };
        open.ty = ownerType;
        open.request = CoreRequest::Value;
        open.knownCount = 3;
        auto call = Inst(opcode, opcode == GirOp::CallConstruct ? 5 : -1);
        call.idx = 2;
        call.vals = { 2, 0, 1 };
        call.vals2 = { 4 };
        auto publish = Inst(GirOp::DestPublish, -1, 5);
        auto leave = Inst(GirOp::Leave);
        leave.idx = 0;
        caller.blocks = { { { { 0, slice }, { 1, slice } }, { enter, initialize, address, count, open, call } } };
        if (opcode == GirOp::Invoke) {
            caller.blocks[0].insts.back().a = 1;
            caller.blocks.push_back({ { { 5, built } }, { publish, leave, Inst(GirOp::Ret) } });
        } else caller.blocks[0].insts.insert(caller.blocks[0].insts.end(), { publish, leave, Inst(GirOp::Ret) });
        module.funcs.push_back(caller);
        GirFunc callee;
        callee.name = "constructing_region_callee";
        callee.params = { holder, slice, slice };
        callee.results = { ownerType };
        callee.resultProtocols = { { CoreRequest::Value, nullopt } };
        callee.roots.results = { {} };
        callee.roots.contents = { { 0, { { CoreRootRef::Param, 1 }, { CoreRootRef::Param, 2 } } } };
        callee.scopes = { -1 };
        callee.summary.constructs = { 0 };
        auto value = Inst(GirOp::Int, 4);
        value.ty = integer;
        value.text = "7";
        auto write = Inst(GirOp::DestWrite, -1, 3, 4);
        auto finish = Inst(GirOp::DestFinish, 5, 3);
        auto ret = Inst(GirOp::Ret);
        ret.vals = { 5 };
        callee.blocks = { { { { 0, holder }, { 1, slice }, { 2, slice }, { 3, destination } },
            { enter, value, write, finish, leave, ret } } };
        module.funcs.push_back(callee);
        assert(Code(module) == "GIR-V050");
        module.funcs[1].roots.slots->at(0).second.push_back({ CoreRootRef::Param, 1 });
        assert(Code(module).empty());
    }
}

void RejectsNestedReferenceParameters() {
    auto module = Module();
    module.globals.push_back(IntegerGlobal(module));
    auto integer = module.globals[0].ty;
    auto reference = module.RefType(CoreMut::Mut, integer);
    auto nested = module.RefType(CoreMut::Mut, reference);
    auto &entry = module.funcs[0];
    entry.slots = { { reference, CoreVarKind::Var, 0, 0 } };
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto global = Inst(GirOp::Global, 0);
    global.idx = 0;
    auto initialize = Inst(GirOp::Init, -1, 0);
    initialize.idx = 0;
    auto holder = Inst(GirOp::Slot, 1);
    holder.idx = 0;
    auto call = Inst(GirOp::Call);
    call.idx = 1;
    call.vals = { 1 };
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    entry.blocks = { { {}, { enter, global, initialize, holder, call, leave, Inst(GirOp::Ret) } } };
    GirFunc callee;
    callee.name = "nested_reference_writer";
    callee.params = { nested };
    callee.scopes = { -1 };
    callee.summary.reads = { { false, 0 } };
    auto value = Inst(GirOp::Int, 2);
    value.ty = integer;
    value.text = "7";
    callee.blocks = { { { { 0, nested } }, { Inst(GirOp::Load, 1, 0), value,
        Inst(GirOp::Store, -1, 1, 2), Inst(GirOp::Ret) } } };
    module.funcs.push_back(callee);
    assert(Code(module) == "GIR-V010");
    module.funcs[0] = Module().funcs[0];
    module.funcs[1].blocks[0].insts = { Inst(GirOp::Ret) };
    module.types[nested].elem = -1;
    assert(Code(module) == "GIR-V010");
}

GirModule SpecializedContentCorrelation(bool nested) {
    auto module = GlobalEmptyContentReplacement();
    auto other = module.globals[0];
    other.name = "other";
    module.globals.push_back(std::move(other));
    auto integer = module.Type(module.globals[0].ty).elem;
    auto slice = module.SliceType(CoreMut::Mut, integer);
    auto holder = module.RefType(CoreMut::Mut, slice);
    module.funcs.clear();
    GirFunc caller;
    caller.name = "specialized_correlation_caller";
    caller.scopes = { -1 };
    caller.slots = { { slice, CoreVarKind::Var, 0, 0 } };
    caller.roots.slots = vector<pair<int, vector<CoreRootRef>>> { { 0, { { CoreRootRef::Global, 1 } } } };
    caller.summary.reads = { { true, 0 }, { true, 1 } };
    caller.summary.writes = { { true, 1 } };
    caller.summary.aborts = true;
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto global = Inst(GirOp::Global, 0);
    global.idx = 1;
    auto initial = Inst(GirOp::ViewSlice, 2, 1);
    initial.mut = CoreMut::Mut;
    auto initialize = Inst(GirOp::Init, -1, 2);
    initialize.idx = 0;
    auto address = Inst(GirOp::Slot, 3);
    address.idx = 0;
    auto call = Inst(GirOp::Call, nested ? 4 : -1);
    call.idx = 1;
    call.vals = { 3, 2 };
    auto zero = Inst(GirOp::Int, 6);
    zero.ty = integer;
    zero.text = "0";
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    vector<GirInst> body = { enter, global, Inst(GirOp::Snap, 1, 0), initial, initialize, address, call };
    if (!nested) body.push_back(Inst(GirOp::Load, 4, 3));
    body.insert(body.end(), { Inst(GirOp::SliceView, 5, 4), zero, Inst(GirOp::Index, 7, 5, 6),
        Inst(GirOp::Store, -1, 7, 6), leave, Inst(GirOp::Ret) });
    caller.blocks = { { {}, body } };
    module.funcs.push_back(caller);
    GirFunc callee;
    callee.name = "specialized_correlation_callee";
    callee.params = { holder, slice };
    callee.scopes = { -1 };
    callee.roots.params = { { 1, { { CoreRootRef::Global, 0 }, { CoreRootRef::Global, 1 } } } };
    callee.roots.contents = { { 0, { { CoreRootRef::Param, 1 } } } };
    callee.roots.slots.emplace();
    callee.summary.reads = { { true, 0 } };
    callee.summary.writes = { { false, 0 } };
    callee.summary.rebinds = { { false, 0 } };
    callee.summary.aborts = true;
    if (nested) {
        callee.results = { slice };
        callee.roots.results = { { { CoreRootRef::Param, 1 } } };
        callee.summary.reads.push_back({ false, 0 });
        auto inner = Inst(GirOp::Call);
        inner.idx = 2;
        inner.vals = { 0 };
        auto ret = Inst(GirOp::Ret);
        ret.vals = { 2 };
        callee.blocks = { { { { 0, holder }, { 1, slice } }, { inner, Inst(GirOp::Load, 2, 0), ret } } };
        module.funcs.push_back(callee);
    }
    auto target = nested ? 1 : 2;
    auto source = Inst(GirOp::Global, target);
    source.idx = 0;
    auto payload = Inst(GirOp::ViewSlice, target + 2, target + 1);
    payload.mut = CoreMut::Mut;
    GirFunc writer = callee;
    writer.name = "literal_specialized_writer";
    writer.results.clear();
    writer.roots.results.clear();
    if (nested) {
        writer.params = { holder };
        writer.roots.params.clear();
        writer.roots.contents = { { 0, { { CoreRootRef::Global, 0 }, { CoreRootRef::Global, 1 } } } };
        writer.summary.reads = { { true, 0 } };
    }
    vector<pair<int, GirTypeId>> parameters { { 0, holder } };
    if (!nested) parameters.push_back({ 1, slice });
    writer.blocks = { { parameters, { source, Inst(GirOp::Snap, target + 1, target), payload,
        Inst(GirOp::Store, -1, 0, target + 2), Inst(GirOp::Ret) } } };
    module.funcs.push_back(writer);
    return module;
}

GirModule SymbolicReturnedContentCorrelation() {
    auto module = GlobalEmptyContentReplacement();
    auto other = module.globals[0];
    other.name = "other";
    module.globals.push_back(std::move(other));
    auto integer = module.Type(module.globals[0].ty).elem;
    auto slice = module.SliceType(CoreMut::Mut, integer);
    auto holder = module.RefType(CoreMut::Mut, slice);
    vector<CoreRootRef> globals { { CoreRootRef::Global, 0 }, { CoreRootRef::Global, 1 } };
    for (auto &global : module.globals) {
        auto zero = Inst(GirOp::Int, 0);
        zero.ty = integer;
        zero.text = "0";
        auto array = Inst(GirOp::Arr, 1);
        array.ty = global.ty;
        array.vals = { 0 };
        auto ret = Inst(GirOp::Ret);
        ret.vals = { 1 };
        global.init.blocks = { { {}, { zero, array, ret } } };
    }
    module.funcs.clear();
    GirFunc caller;
    caller.name = "returned_content_caller";
    caller.scopes = { -1 };
    caller.slots = { { slice, CoreVarKind::Var, 0, 0 }, { slice, CoreVarKind::Var, 0, 1 } };
    caller.roots.slots = vector<pair<int, vector<CoreRootRef>>> {
        { 0, globals }, { 1, { { CoreRootRef::Global, 1 } } } };
    caller.summary.reads = { { true, 0 }, { true, 1 } };
    caller.summary.writes = { { true, 1 } };
    caller.summary.aborts = true;
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto first = Inst(GirOp::Global, 0);
    first.idx = 0;
    auto firstSlice = Inst(GirOp::ViewSlice, 2, 1);
    firstSlice.mut = CoreMut::Mut;
    auto firstInit = Inst(GirOp::Init, -1, 2);
    firstInit.idx = 0;
    auto second = Inst(GirOp::Global, 3);
    second.idx = 1;
    auto secondSlice = Inst(GirOp::ViewSlice, 5, 4);
    secondSlice.mut = CoreMut::Mut;
    auto secondInit = Inst(GirOp::Init, -1, 5);
    secondInit.idx = 1;
    auto firstAddress = Inst(GirOp::Slot, 6);
    firstAddress.idx = 0;
    auto secondAddress = Inst(GirOp::Slot, 7);
    secondAddress.idx = 1;
    auto call = Inst(GirOp::Call);
    call.idx = 1;
    call.vals = { 6, 5, 7 };
    auto zero = Inst(GirOp::Int, 10);
    zero.ty = integer;
    zero.text = "0";
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    caller.blocks = { { {}, { enter, first, Inst(GirOp::Snap, 1, 0), firstSlice, firstInit,
        second, Inst(GirOp::Snap, 4, 3), secondSlice, secondInit, firstAddress, secondAddress,
        call, Inst(GirOp::Load, 8, 7), Inst(GirOp::SliceView, 9, 8), zero,
        Inst(GirOp::Index, 11, 9, 10), Inst(GirOp::Store, -1, 11, 10), leave, Inst(GirOp::Ret) } } };
    module.funcs.push_back(caller);
    GirFunc wrapper;
    wrapper.name = "returned_content_wrapper";
    wrapper.params = { holder, slice, holder };
    wrapper.scopes = { -1 };
    wrapper.roots.slots.emplace();
    wrapper.roots.params = { { 1, globals } };
    wrapper.roots.contents = { { 0, globals }, { 2, { { CoreRootRef::Param, 1 } } } };
    wrapper.summary.reads = { { false, 0 } };
    wrapper.summary.writes = { { false, 2 } };
    wrapper.summary.rebinds = { { false, 2 } };
    auto inner = Inst(GirOp::Call, 3);
    inner.idx = 2;
    inner.vals = { 0, 1 };
    wrapper.blocks = { { { { 0, holder }, { 1, slice }, { 2, holder } },
        { inner, Inst(GirOp::Store, -1, 2, 3), Inst(GirOp::Ret) } } };
    module.funcs.push_back(wrapper);
    GirFunc reader;
    reader.name = "symbolic_content_reader";
    reader.params = { holder, slice };
    reader.results = { slice };
    reader.scopes = { -1 };
    reader.roots.slots.emplace();
    reader.roots.params = { { 1, globals } };
    reader.roots.contents = { { 0, { { CoreRootRef::Param, 1 } } } };
    reader.roots.results = { { { CoreRootRef::Param, 1 } } };
    reader.summary.reads = { { false, 0 } };
    auto ret = Inst(GirOp::Ret);
    ret.vals = { 2 };
    reader.blocks = { { { { 0, holder }, { 1, slice } }, { Inst(GirOp::Load, 2, 0), ret } } };
    module.funcs.push_back(reader);
    return module;
}

void PreservesReturnedContentCorrelation() {
    auto module = SymbolicReturnedContentCorrelation();
    auto observed = Code(module);
    if (observed != "GIR-V050") fprintf(stderr, "symbolic returned content: %s\n", observed.empty() ? "accepted" : observed.c_str());
    assert(observed == "GIR-V050");
    vector<CoreRootRef> globals { { CoreRootRef::Global, 0 }, { CoreRootRef::Global, 1 } };
    module.funcs[0].roots.slots->at(1).second = globals;
    module.funcs[0].summary.writes.push_back({ true, 0 });
    module.funcs[1].roots.contents[1].second = globals;
    module.funcs[2].roots.contents[0].second = globals;
    module.funcs[2].roots.results[0] = globals;
    assert(Code(module).empty());
}

void PreservesSpecializedContentCorrelation() {
    for (bool nested : { false, true }) {
        auto module = SpecializedContentCorrelation(nested);
        auto observed = Code(module);
        if (observed != "GIR-V050") fprintf(stderr, "specialized correlation nested=%d: %s\n", nested, observed.c_str());
        assert(observed == "GIR-V050");
        auto &writer = module.funcs[nested ? 2 : 1];
        auto holder = writer.params[0];
        auto slice = module.Type(holder).elem;
        writer.params = { holder, slice };
        writer.roots.contents = { { 0, { { CoreRootRef::Param, 1 } } } };
        writer.blocks = { { { { 0, holder }, { 1, slice } }, { Inst(GirOp::Store, -1, 0, 1), Inst(GirOp::Ret) } } };
        if (nested) module.funcs[1].blocks[0].insts[0].vals = { 0, 1 };
        assert(Code(module).empty());
    }
}

void ChecksDeclaredContentStoresAndCallRegions() {
    auto module = Module();
    auto integer = module.IntType(CoreIntTy::I64);
    auto slice = module.SliceType(CoreMut::Mut, integer);
    auto holder = module.RefType(CoreMut::Mut, slice);
    GirFunc writer;
    writer.name = "region_writer";
    writer.params = { holder, slice };
    writer.scopes = { -1 };
    writer.summary.unknown = true;
    writer.blocks = { { { { 0, holder }, { 1, slice } }, { Inst(GirOp::Store, -1, 0, 1), Inst(GirOp::Ret) } } };
    module.funcs.push_back(writer);
    assert(Code(module) == "GIR-V050");
    module.funcs[0].roots.slots.emplace();
    assert(Code(module) == "GIR-V050");
    module.funcs[1].roots.contents = { { 0, { { CoreRootRef::Param, 1 } } } };
    assert(Code(module).empty());
    module.funcs[1].roots.contents[0].second = { { CoreRootRef::Param, 0 } };
    assert(Code(module) == "GIR-V050");
    module.funcs[1].params = { holder, slice, slice };
    module.funcs[1].blocks = { { { { 0, holder }, { 1, slice }, { 2, slice } }, { Inst(GirOp::Ret) } } };
    module.funcs[1].roots.contents = { { 0, { { CoreRootRef::Param, 1 }, { CoreRootRef::Param, 2 } } } };
    GirFunc caller;
    caller.name = "region_caller";
    caller.params = { slice, slice };
    caller.scopes = { -1 };
    caller.summary.unknown = true;
    caller.slots = { { slice, CoreVarKind::Var, 0, 0 } };
    auto enter = Inst(GirOp::Enter);
    enter.idx = 0;
    auto init = Inst(GirOp::Init, -1, 0);
    init.idx = 0;
    auto address = Inst(GirOp::Slot, 2);
    address.idx = 0;
    auto call = Inst(GirOp::Call);
    call.idx = 1;
    call.vals = { 2, 0, 1 };
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    caller.blocks = { { { { 0, slice }, { 1, slice } }, { enter, init, address, call, leave, Inst(GirOp::Ret) } } };
    module.funcs.push_back(caller);
    assert(Code(module) == "GIR-V050");
    module.funcs[0].roots.slots.reset();
    assert(Code(module) == "GIR-V050");
    module.funcs[0].roots.slots.emplace();
    module.funcs[2].roots.slots = vector<pair<int, vector<CoreRootRef>>> {
        { 0, { { CoreRootRef::Param, 0 }, { CoreRootRef::Param, 1 } } } };
    assert(Code(module).empty());
    module.funcs[2].roots.slots->at(0).second = { { CoreRootRef::Param, 1 } };
    assert(Code(module) == "GIR-V050");
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
    entry.roots.slots = vector<pair<int, vector<CoreRootRef>>> {
        { 0, { { CoreRootRef::Global, 1 } } },
        { 1, { { CoreRootRef::Global, 0 }, { CoreRootRef::Global, 1 } } } };
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
    caller.slots = { { slice, CoreVarKind::Var, 0, 0 }, { slice, CoreVarKind::Let, 0, 1 } };
    caller.roots.slots = vector<pair<int, vector<CoreRootRef>>> {
        { 0, { { CoreRootRef::Global, 1 }, { CoreRootRef::Global, 2 } } },
        { 1, { { CoreRootRef::Global, 1 }, { CoreRootRef::Global, 2 } } } };
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
    read.vals = { 4, 11 };
    auto oldValue = Inst(GirOp::Slot, 10);
    oldValue.idx = 1;
    auto keep = Inst(GirOp::Init, -1, 3);
    keep.idx = 1;
    auto zero = Inst(GirOp::Int, 8);
    zero.ty = integer;
    zero.text = "0";
    auto literal = Inst(GirOp::Arr, 9);
    literal.ty = owner;
    literal.vals = { 8 };
    auto leave = Inst(GirOp::Leave);
    leave.idx = 0;
    caller.blocks = { { {}, { enter, address(0, 0), address(1, 1), Inst(GirOp::Snap, 2, 1), initial,
        slot, initialize, keep, oldValue, Inst(GirOp::Load, 11, 10), address(5, 2), Inst(GirOp::Snap, 6, 5), payload, write,
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
    assert(Code(module) == "GIR-V050");
    module.funcs[3].roots.params.clear();
    assert(Code(module) == "GIR-V060");
}

void ChecksActualHolderAliasesAfterCallWrites() {
    for (bool aliased : { false, true })
        assert(Code(ActualHolderAliasModule(aliased)) == (aliased ? "GIR-V050" : ""));
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
        assert(Code(module) == (aliased ? "GIR-V050" : ""));
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
    PreservesLeastActualReturnRoots();
    PreservesReturnedContentCorrelation();
    PreservesSpecializedContentCorrelation();
    RejectsNestedReferenceParameters();
    NormalizesRawSpecializedCallContentRegions();
    ChecksConstructingCallContentRegions();
    ChecksEveryPossibleContentReceiver();
    NormalizesSpecializedForwardContentRegions();
    AdmitsMixedSelfSourceArgumentRegions();
    PreservesWidenedSourceLocalContentRegions();
    ChecksDeclaredContentStoresAndCallRegions();
    EnforcesDeclaredRegionCeilings();
    PreservesOptionalSlotRootMetadata();
    PreservesOptionalValueRootMetadata();
    EnforcesSourceValueRootCeilings();
    RejectsWideValueRootsAtNarrowSlots();
    LowersStoppedConditionalRootsPerContext();
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
