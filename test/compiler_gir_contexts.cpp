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

CoreExprP Integer(CoreTypeId type, const char *value) {
    auto expression = make_unique<CoreExpr>();
    expression->kind = CoreExprKind::Lit;
    expression->type = type;
    expression->value = value;
    return expression;
}

CorePlaceP Global(int index) {
    auto place = make_unique<CorePlace>();
    place->kind = CorePlace::Global;
    place->index = index;
    return place;
}

CoreModule SharedContextModule(int selectedContext, int selectedGlobal, bool genericFirst = false,
                               bool emptyFirst = false, bool omitFirst = false) {
    CoreModule core;
    core.files = { "contexts.goose" };
    auto integer = core.IntType(CoreIntTy::I64);
    auto unit = core.UnitType();
    CoreType referenceType;
    referenceType.kind = CoreType::Ref;
    referenceType.mut = CoreMut::Mut;
    referenceType.elem = integer;
    auto reference = core.Intern(referenceType);
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Expr };

    CoreImpl main;
    main.name = "main";
    main.body.scope = 0;
    auto call = make_unique<CoreExpr>();
    call->kind = CoreExprKind::Call;
    call->ctx = selectedContext;
    call->type = unit;
    call->org = origin;
    call->args.push_back(CoreArgReference { CoreMut::Mut, Global(selectedGlobal) });
    CoreStmt evaluate;
    evaluate.kind = CoreStmtKind::Expr;
    evaluate.expr = std::move(call);
    evaluate.org = origin;
    main.body.stmts.push_back(std::move(evaluate));
    main.summary.reads = { CoreTarget { true, selectedGlobal } };

    CoreImpl receiver;
    receiver.name = "receiver";
    receiver.params = { CoreParam { 0, true } };
    receiver.vars = { CoreVar { "reference", reference, CoreVarKind::Let, 0, origin } };
    receiver.body.scope = 0;
    receiver.summary.reads = { CoreTarget { false, 0 } };

    core.impls.push_back(std::move(main));
    core.impls.push_back(std::move(receiver));
    CoreContext entry;
    entry.impl = 0;
    entry.stablekey = "entry-key";
    entry.module = "app";
    CoreContext first;
    first.impl = 1;
    first.stablekey = "receiver-a-key";
    first.module = "lib-a";
    if (!omitFirst) {
        vector<CoreRootRef> roots;
        if (genericFirst) roots = { CoreRootRef { CoreRootRef::Param, 0 } };
        else if (!emptyFirst) roots = { CoreRootRef { CoreRootRef::Global, 0 } };
        first.varroots = { { 0, std::move(roots) } };
    }
    CoreContext second;
    second.impl = 1;
    second.stablekey = "receiver-b-key";
    second.module = "lib-b";
    second.varroots = { { 0, { CoreRootRef { CoreRootRef::Global, 1 } } } };
    core.contexts = { std::move(entry), std::move(first), std::move(second) };
    core.entry = 0;

    for (int index = 0; index < 2; index++) {
        CoreGlobal global;
        global.name = index == 0 ? "left" : "right";
        global.type = integer;
        global.kind = CoreVarKind::Var;
        global.init = Integer(integer, index == 0 ? "1" : "2");
        global.org = origin;
        core.globals.push_back(std::move(global));
    }
    return core;
}

GirModule Lower(const CoreModule &core) {
    return GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Expr } },
        [](const CoreOrigin &) { return 0; }).Lower();
}

string Code(GirModule module) {
    auto violation = GirVerifier(module).Verify();
    return violation ? violation->code : "";
}

const GirInst &Call(const GirFunc &function) {
    for (auto &block : function.blocks)
        for (auto &instruction : block.insts)
            if (instruction.op == GirOp::Call || instruction.op == GirOp::CallConstruct || instruction.op == GirOp::Invoke) return instruction;
    assert(false);
    return function.blocks[0].insts[0];
}

const vector<CoreRootRef> *ParamRoots(const GirFunc &function, int parameter) {
    auto row = find_if(function.roots.params.begin(), function.roots.params.end(),
        [&](auto &entry) { return entry.first == parameter; });
    return row == function.roots.params.end() ? nullptr : &row->second;
}

void SharedImplementationsKeepContextRootsAndCallIndices() {
    auto high = Lower(SharedContextModule(1, 0));
    assert(high.funcs.size() == 3);
    assert(high.entry == 0);
    assert(Code(high).empty());
    vector<CoreRootRef> globalZero { CoreRootRef { CoreRootRef::Global, 0 } };
    vector<CoreRootRef> globalOne { CoreRootRef { CoreRootRef::Global, 1 } };
    assert(ParamRoots(high.funcs[1], 0) && *ParamRoots(high.funcs[1], 0) == globalZero);
    assert(ParamRoots(high.funcs[2], 0) && *ParamRoots(high.funcs[2], 0) == globalOne);
    assert(high.funcs[1].key == "receiver-a-key" && high.funcs[1].module == "lib-a");
    assert(high.funcs[2].key == "receiver-b-key" && high.funcs[2].module == "lib-b");
    assert(Call(high.funcs[0]).idx == 1);

    auto selected = Lower(SharedContextModule(2, 1));
    assert(Code(selected).empty());
    assert(Call(selected.funcs[0]).idx == 2);
}

CoreModule ConstructionTargetContexts() {
    CoreModule core;
    core.profile = CoreProfile::Construction;
    core.files = { "target-contexts.goose" };
    core.types = { CoreType { .kind = CoreType::Int, .ity = CoreIntTy::I64 },
                   CoreType { .kind = CoreType::Grow, .elem = 0 }, CoreType { .kind = CoreType::Unit } };
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Expr };

    CoreImpl main;
    main.name = "main";
    main.body.scope = 0;
    main.vars = { CoreVar { "result", 1, CoreVarKind::Let, 0, origin } };
    auto producer = make_unique<CoreExpr>();
    producer->kind = CoreExprKind::Call;
    producer->ctx = 2;
    producer->type = 1;
    producer->org = origin;
    CoreStmt receive;
    receive.kind = CoreStmtKind::Let;
    receive.var = 0;
    receive.expr = std::move(producer);
    receive.org = origin;
    main.body.stmts.push_back(std::move(receive));

    CoreImpl target;
    target.name = "target";
    target.body.scope = 0;
    target.results = { CoreResultDescriptor { 1, CoreRequest::Value, nullopt } };
    target.summary.constructs = { 0 };
    auto helperCall = make_unique<CoreExpr>();
    helperCall->kind = CoreExprKind::Call;
    helperCall->ctx = 3;
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
    array->elems.push_back(Integer(0, "7"));
    CoreStmt escape;
    escape.kind = CoreStmtKind::ReturnFrom;
    escape.target = 0;
    escape.values.push_back(std::move(array));
    escape.org = origin;

    core.impls.push_back(std::move(main));
    core.impls.push_back(std::move(target));
    core.impls.push_back(std::move(helper));
    core.contexts = { CoreContext { .impl = 0 }, CoreContext { .impl = 1 },
                      CoreContext { .impl = 1 }, CoreContext { .impl = 2 } };
    core.targets = { CoreTargetSet { { 1 } } };
    core.impls[2].body.stmts.push_back(std::move(escape));
    return core;
}

void ConstructionTargetsIncludeEveryMemberContext() {
    auto high = Lower(ConstructionTargetContexts());
    assert(Code(high).empty());
    assert(high.funcs.size() == 4);
    assert(high.entry == 0);
    assert(high.targets.size() == 1);
    vector<int> memberContexts { 1, 2 };
    assert(high.targets[0].members == memberContexts);
    assert(Call(high.funcs[0]).idx == 2);
    auto low = GirToLow(high).Lower();
    assert(Code(low).empty());
    assert(low.lowtargets.size() == 1);
    assert(low.lowtargets[0].members == memberContexts);
}

void GenericAndEmptyContextRootsRemainDistinct() {
    auto generic = Lower(SharedContextModule(1, 0, true));
    assert(Code(generic).empty());
    vector<CoreRootRef> genericRoot { CoreRootRef { CoreRootRef::Param, 0 } };
    assert(ParamRoots(generic.funcs[1], 0) && *ParamRoots(generic.funcs[1], 0) == genericRoot);

    auto explicitEmpty = Lower(SharedContextModule(2, 1, false, true));
    assert(Code(explicitEmpty).empty());
    assert(ParamRoots(explicitEmpty.funcs[1], 0));
    assert(ParamRoots(explicitEmpty.funcs[1], 0)->empty());

    auto rejectedEmpty = Lower(SharedContextModule(1, 0, false, true));
    assert(Code(rejectedEmpty) == "GIR-V050");

    auto absent = Lower(SharedContextModule(1, 0, false, false, true));
    assert(Code(absent).empty());
    assert(ParamRoots(absent.funcs[1], 0) == nullptr);
}

}

int main() {
    SharedImplementationsKeepContextRootsAndCallIndices();
    ConstructionTargetsIncludeEveryMemberContext();
    GenericAndEmptyContextRootsRemainDistinct();
    puts("compiler_gir_contexts ok");
    return 0;
}
