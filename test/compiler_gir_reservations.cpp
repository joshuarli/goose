#ifdef NDEBUG
#undef NDEBUG
#endif
#include "../src/includes.h"
#include "../src/utils.h"
#include "../src/small_vector.h"
#include "../src/flat_map.h"
#include "../src/lexer.h"
#include "../src/ast.h"
#include "../src/report/hooks.h"
#include "../src/units/options.h"
#include "../src/ident/keys.h"
#include "../src/ident/deps.h"
#include "../src/dump.h"
#include "../src/clone.h"
#include "../src/parser.h"
#include "../src/resolve.h"
#include "../src/builtins.h"
#include "../src/gfx.h"
#include "../src/typecheck.h"
#include "../src/typecheck_types.h"
#include "../src/typecheck_exprs.h"
#include "../src/typecheck_expansion.h"
#include "../src/typecheck_flow.h"
#include "../src/typecheck_calls.h"
#include "../src/typecheck_builtins.h"
#include "../src/typecheck_nodes.h"
#include "../src/optimize.h"
#include "../src/optimize_basecase.h"
#include "../src/optimize_tre.h"
#include "../src/optimize_loops.h"
#include "../src/optimize_reassoc.h"
#include "../src/bce.h"
#include "../src/codegen.h"
#include "../src/codegen_types.h"
#include "../src/codegen_frames.h"
#include "../src/codegen_values.h"
#include "../src/codegen_construct.h"
#include "../src/codegen_stmts.h"
#include "../src/codegen_calls.h"
#include "../src/codegen_builtins.h"
#include "../src/codegen_render.h"
#include "../src/codegen_emit.h"
#include "../src/codegen_stacks.h"
#include "../src/codegen_nodes.h"
#include "../src/runtime_inline.h"
#include "../src/units/postpass.h"
#include "../src/units/emit.h"
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
#include "../src/gir/c/gir_c.h"

using namespace goose;

extern "C" gs_shaderc_result gs_shaderc_compile(const char *, const char *, int) {
    return { nullptr, 0, nullptr };
}

extern "C" void gs_shaderc_free(gs_shaderc_result *) {}

namespace {

const CoreOrigin origin { 0, 1, CoreOriginKind::Expr };

CoreExprP Integer(CoreTypeId type, const char *value) {
    auto expression = make_unique<CoreExpr>();
    expression->kind = CoreExprKind::Lit;
    expression->type = type;
    expression->value = value;
    return expression;
}

CoreExprP Bytes(CoreTypeId type, uint8_t value) {
    auto expression = make_unique<CoreExpr>();
    expression->kind = CoreExprKind::Bytes;
    expression->type = type;
    expression->bytes = { value };
    expression->org = origin;
    return expression;
}

CoreModule InterruptedReturn(CoreStmtKind interruption, bool nested = false) {
    CoreModule core;
    core.profile = CoreProfile::Construction;
    core.files = { "interrupted-return.goose" };
    auto u8 = core.IntType(CoreIntTy::U8);
    auto i64 = core.IntType(CoreIntTy::I64);
    auto bytes = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = u8 });
    CoreImpl entry;
    entry.name = "entry";
    entry.body.scope = 0;
    entry.vars = { CoreVar { "output", bytes, CoreVarKind::Var, 0, origin } };
    entry.summary.unknown = true;
    CoreStmt receive;
    receive.kind = CoreStmtKind::Let;
    receive.var = 0;
    receive.org = origin;
    receive.expr = make_unique<CoreExpr>();
    receive.expr->kind = CoreExprKind::Call;
    receive.expr->type = bytes;
    receive.expr->ctx = 1;
    receive.expr->org = origin;
    entry.body.stmts.push_back(std::move(receive));
    CorePrintArg view;
    view.kind = CorePrintArg::View;
    view.view = make_unique<CoreView>();
    view.view->place = make_unique<CorePlace>();
    view.view->place->index = 0;
    CoreStmt print;
    print.kind = CoreStmtKind::Print;
    print.org = origin;
    print.print.push_back(std::move(view));
    entry.body.stmts.push_back(std::move(print));
    CoreImpl producer;
    producer.name = "producer";
    producer.body.scope = 0;
    producer.results = { CoreResultDescriptor { bytes, CoreRequest::Value } };
    producer.vars = { CoreVar { "index", i64, CoreVarKind::Var, 1, origin } };
    producer.summary.constructs = { 0 };
    auto element = make_unique<CoreExpr>();
    element->kind = CoreExprKind::Block;
    element->type = u8;
    element->org = origin;
    element->then = make_unique<CoreBlock>();
    element->then->scope = 2;
    CoreStmt interrupt;
    interrupt.kind = interruption;
    interrupt.org = origin;
    if (nested) {
        producer.vars.push_back(CoreVar { "local", bytes, CoreVarKind::Var, 2, origin });
        CoreStmt local;
        local.kind = CoreStmtKind::Let;
        local.var = 1;
        local.org = origin;
        local.expr = make_unique<CoreExpr>();
        local.expr->kind = CoreExprKind::Arr;
        local.expr->type = bytes;
        local.expr->org = origin;
        local.expr->elems.push_back(Integer(u8, "70"));
        auto inner = make_unique<CoreExpr>();
        inner->kind = CoreExprKind::Block;
        inner->type = u8;
        inner->org = origin;
        inner->then = make_unique<CoreBlock>();
        inner->then->scope = 3;
        inner->then->stmts.push_back(std::move(interrupt));
        inner->then->value = Integer(u8, "66");
        local.expr->elems.push_back(std::move(inner));
        element->then->stmts.push_back(std::move(local));
    } else element->then->stmts.push_back(std::move(interrupt));
    element->then->value = Integer(u8, "66");
    auto array = make_unique<CoreExpr>();
    array->kind = CoreExprKind::Arr;
    array->type = bytes;
    array->org = origin;
    array->elems.push_back(Integer(u8, "65"));
    array->elems.push_back(std::move(element));
    CoreStmt returned;
    returned.kind = CoreStmtKind::RetValues;
    returned.org = origin;
    returned.values.push_back(std::move(array));
    CoreStmt loop;
    loop.kind = CoreStmtKind::ForRange;
    loop.var = 0;
    loop.expr = Integer(i64, "0");
    loop.expr2 = Integer(i64, "1");
    loop.org = origin;
    loop.then = make_unique<CoreBlock>();
    loop.then->scope = 1;
    loop.then->stmts.push_back(std::move(returned));
    producer.body.stmts.push_back(std::move(loop));
    CoreStmt final;
    final.kind = CoreStmtKind::RetValues;
    final.org = origin;
    final.values.push_back(Bytes(bytes, 67));
    producer.body.stmts.push_back(std::move(final));
    core.impls.push_back(std::move(entry));
    core.impls.push_back(std::move(producer));
    core.contexts = { CoreContext { .impl = 0 }, CoreContext { .impl = 1, .resultroots = { {} } } };
    return core;
}

CoreModule InterruptedCall() {
    CoreModule core;
    core.profile = CoreProfile::Construction;
    core.files = { "interrupted-call.goose" };
    auto bytes = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = core.IntType(CoreIntTy::U8) });
    auto i64 = core.IntType(CoreIntTy::I64);
    auto call = [&](int context) {
        auto expression = make_unique<CoreExpr>();
        expression->kind = CoreExprKind::Call;
        expression->type = bytes;
        expression->ctx = context;
        expression->org = origin;
        return expression;
    };
    CoreImpl entry;
    entry.name = "entry";
    entry.body.scope = 0;
    entry.summary.unknown = true;
    entry.vars = { { "first", bytes, CoreVarKind::Var, 0, origin }, { "second", bytes, CoreVarKind::Var, 0, origin } };
    CoreStmt receive;
    receive.kind = CoreStmtKind::Receive;
    receive.vars = { 0, 1 };
    receive.expr = call(1);
    receive.org = origin;
    entry.body.stmts.push_back(std::move(receive));
    CoreStmt print;
    print.kind = CoreStmtKind::Print;
    print.org = origin;
    for (int index : { 0, 1 }) {
        CorePrintArg view;
        view.kind = CorePrintArg::View;
        view.view = make_unique<CoreView>();
        view.view->place = make_unique<CorePlace>();
        view.view->place->index = index;
        print.print.push_back(std::move(view));
    }
    entry.body.stmts.push_back(std::move(print));
    CoreImpl producer;
    producer.name = "producer";
    producer.body.scope = 0;
    producer.summary.constructs = { 0, 1 };
    producer.results = { { bytes, CoreRequest::Value, 0 }, { bytes, CoreRequest::Value } };
    producer.vars = { { "result", bytes, CoreVarKind::Var, 0, origin }, { "index", i64, CoreVarKind::Var, 1, origin } };
    CoreStmt initial;
    initial.kind = CoreStmtKind::Let;
    initial.var = 0;
    initial.org = origin;
    initial.expr = Bytes(bytes, 65);
    producer.body.stmts.push_back(std::move(initial));
    CoreStmt loop;
    loop.kind = CoreStmtKind::ForRange;
    loop.var = 1;
    loop.expr = Integer(i64, "0");
    loop.expr2 = Integer(i64, "1");
    loop.org = origin;
    loop.then = make_unique<CoreBlock>();
    loop.then->scope = 1;
    auto block = make_unique<CoreExpr>();
    block->kind = CoreExprKind::Block;
    block->type = bytes;
    block->org = origin;
    block->then = make_unique<CoreBlock>();
    block->then->scope = 2;
    CoreStmt stop;
    stop.kind = CoreStmtKind::Break;
    stop.org = origin;
    block->then->stmts.push_back(std::move(stop));
    block->then->value = Bytes(bytes, 67);
    CoreStmt interrupted;
    interrupted.kind = CoreStmtKind::RetValues;
    interrupted.org = origin;
    interrupted.values.push_back(call(2));
    interrupted.values.push_back(std::move(block));
    loop.then->stmts.push_back(std::move(interrupted));
    producer.body.stmts.push_back(std::move(loop));
    CoreStmt final;
    final.kind = CoreStmtKind::RetValues;
    final.org = origin;
    auto named = make_unique<CoreExpr>();
    named->kind = CoreExprKind::ResultLocal;
    named->type = bytes;
    named->var = 0;
    named->org = origin;
    final.values.push_back(std::move(named));
    final.values.push_back(Bytes(bytes, 68));
    producer.body.stmts.push_back(std::move(final));
    CoreImpl helper;
    helper.name = "helper";
    helper.body.scope = 0;
    helper.summary.constructs = { 0 };
    helper.results = { { bytes, CoreRequest::Value } };
    helper.body.value = Bytes(bytes, 66);
    core.impls.push_back(std::move(entry));
    core.impls.push_back(std::move(producer));
    core.impls.push_back(std::move(helper));
    core.contexts = { CoreContext { .impl = 0 }, CoreContext { .impl = 1, .resultroots = { {}, {} } }, CoreContext { .impl = 2, .resultroots = { {} } } };
    return core;
}

CoreModule NamedBorrowGrowth() {
    auto core = InterruptedReturn(CoreStmtKind::Break);
    auto u8 = core.IntType(CoreIntTy::U8);
    auto grow = core.Intern(CoreType { .kind = CoreType::Grow, .elem = u8 });
    auto reference = core.Intern(CoreType { .kind = CoreType::Ref, .mut = CoreMut::Mut, .elem = grow });
    auto elementReference = core.Intern(CoreType { .kind = CoreType::Ref, .mut = CoreMut::Mut, .elem = u8 });
    auto unit = core.Intern(CoreType { .kind = CoreType::Unit });
    core.files = { "named-borrow-growth.goose" };
    auto &entry = core.impls[0];
    entry.vars[0].type = grow;
    entry.body.stmts[0].expr->type = grow;
    auto &producer = core.impls[1];
    producer.results = { { grow, CoreRequest::Value, 0 } };
    producer.vars = { { "result", grow, CoreVarKind::Var, 0, origin } };
    producer.body.stmts.clear();
    CoreStmt initial;
    initial.kind = CoreStmtKind::Let;
    initial.var = 0;
    initial.org = origin;
    initial.expr = make_unique<CoreExpr>();
    initial.expr->kind = CoreExprKind::Arr;
    initial.expr->type = grow;
    initial.expr->org = origin;
    initial.expr->elems.push_back(Integer(u8, "65"));
    producer.body.stmts.push_back(std::move(initial));
    CoreStmt borrow;
    borrow.kind = CoreStmtKind::Expr;
    borrow.org = origin;
    borrow.expr = make_unique<CoreExpr>();
    borrow.expr->kind = CoreExprKind::Call;
    borrow.expr->type = unit;
    borrow.expr->ctx = 2;
    borrow.expr->org = origin;
    CoreArgReference argument;
    argument.place = make_unique<CorePlace>();
    argument.place->index = 0;
    borrow.expr->args.push_back(std::move(argument));
    producer.body.stmts.push_back(std::move(borrow));
    CoreStmt final;
    final.kind = CoreStmtKind::RetValues;
    final.org = origin;
    auto named = make_unique<CoreExpr>();
    named->kind = CoreExprKind::ResultLocal;
    named->type = grow;
    named->var = 0;
    named->org = origin;
    final.values.push_back(std::move(named));
    producer.body.stmts.push_back(std::move(final));
    CoreImpl helper;
    helper.name = "extend";
    helper.body.scope = 0;
    helper.vars = { { "values", reference, CoreVarKind::Let, 0, origin } };
    helper.params = { { 0, true } };
    helper.summary.writes = { { false, 0 } };
    helper.summary.grows = { { false, 0 } };
    CoreStmt push;
    push.kind = CoreStmtKind::Expr;
    push.org = origin;
    push.expr = make_unique<CoreExpr>();
    push.expr->kind = CoreExprKind::Push;
    push.expr->type = elementReference;
    push.expr->org = origin;
    push.expr->a = Integer(u8, "68");
    push.expr->place = make_unique<CorePlace>();
    push.expr->place->kind = CorePlace::Deref;
    push.expr->place->expr = make_unique<CoreExpr>();
    push.expr->place->expr->kind = CoreExprKind::Read;
    push.expr->place->expr->type = reference;
    push.expr->place->expr->place = make_unique<CorePlace>();
    helper.body.stmts.push_back(std::move(push));
    core.impls.push_back(std::move(helper));
    CoreContext context;
    context.impl = 2;
    context.varroots = { { 0, { { CoreRootRef::Param, 0 } } } };
    core.contexts.push_back(std::move(context));
    return core;
}

CoreModule InterruptedOwnerChild(bool named) {
    auto core = InterruptedReturn(CoreStmtKind::Break);
    auto u8 = core.IntType(CoreIntTy::U8);
    auto i64 = core.IntType(CoreIntTy::I64);
    auto inner = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = u8 });
    auto outer = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = inner });
    auto owner = core.Intern(CoreType { .kind = CoreType::Grow, .elem = inner });
    auto reference = core.Intern(CoreType { .kind = CoreType::Ref, .mut = CoreMut::Mut, .elem = inner });
    core.files = { "interrupted-owner-child.goose" };
    core.impls[1].summary.aborts = true;
    core.impls[0].vars[0].type = outer;
    core.impls[0].body.stmts[0].expr->type = outer;
    auto &producer = core.impls[1];
    producer.results = { { outer, CoreRequest::Value, 0 } };
    producer.vars = { { "result", owner, CoreVarKind::Var, 0, origin }, { "index", i64, CoreVarKind::Var, 1, origin } };
    producer.body.stmts.clear();
    auto result = [&]() {
        auto value = make_unique<CoreExpr>();
        value->kind = CoreExprKind::ResultLocal;
        value->type = owner;
        value->var = 0;
        value->org = origin;
        return value;
    };
    CoreStmt initial;
    initial.kind = CoreStmtKind::Let;
    initial.var = 0;
    initial.org = origin;
    initial.expr = make_unique<CoreExpr>();
    initial.expr->kind = CoreExprKind::Arr;
    initial.expr->type = owner;
    initial.expr->org = origin;
    initial.expr->elems.push_back(Bytes(inner, 65));
    producer.body.stmts.push_back(std::move(initial));
    auto push = [&](CoreExprP value) {
        CoreStmt statement;
        statement.kind = CoreStmtKind::Expr;
        statement.org = origin;
        statement.expr = make_unique<CoreExpr>();
        statement.expr->kind = CoreExprKind::Push;
        statement.expr->type = reference;
        statement.expr->org = origin;
        statement.expr->place = make_unique<CorePlace>();
        statement.expr->place->index = 0;
        statement.expr->a = std::move(value);
        return statement;
    };
    CoreStmt loop;
    loop.kind = CoreStmtKind::ForRange;
    loop.var = 1;
    loop.expr = Integer(i64, "0");
    loop.expr2 = Integer(i64, "1");
    loop.org = origin;
    loop.then = make_unique<CoreBlock>();
    loop.then->scope = 1;
    auto operand = make_unique<CoreExpr>();
    operand->kind = CoreExprKind::Arr;
    operand->type = inner;
    operand->org = origin;
    operand->elems.push_back(Integer(u8, "66"));
    auto block = make_unique<CoreExpr>();
    block->kind = CoreExprKind::Block;
    block->type = u8;
    block->org = origin;
    block->then = make_unique<CoreBlock>();
    block->then->scope = 2;
    CoreStmt stop;
    stop.kind = named ? CoreStmtKind::RetValues : CoreStmtKind::Break;
    stop.org = origin;
    if (named) stop.values.push_back(result());
    block->then->stmts.push_back(std::move(stop));
    block->then->value = Integer(u8, "67");
    operand->elems.push_back(std::move(block));
    loop.then->stmts.push_back(push(std::move(operand)));
    producer.body.stmts.push_back(std::move(loop));
    producer.body.stmts.push_back(push(Bytes(inner, 68)));
    CoreStmt final;
    final.kind = CoreStmtKind::RetValues;
    final.org = origin;
    final.values.push_back(result());
    producer.body.stmts.push_back(std::move(final));
    return core;
}

CoreModule CrossActivationNamed(bool sameIdentity = true) {
    CoreModule core;
    core.profile = CoreProfile::Construction;
    core.files = { "cross-named.goose" };
    auto u8 = core.IntType(CoreIntTy::U8);
    auto bytes = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = u8 });
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Expr };
    auto call = [&](int context) {
        auto value = make_unique<CoreExpr>(); value->kind = CoreExprKind::Call;
        value->ctx = context; value->type = bytes; value->org = origin; return value;
    };
    auto named = [&] {
        auto value = make_unique<CoreExpr>(); value->kind = CoreExprKind::ResultLocal;
        value->var = 0; value->type = bytes; value->org = origin; return value;
    };
    CoreImpl entry;
    entry.name = "main"; entry.body.scope = 0;
    entry.vars = { CoreVar { "output", bytes, CoreVarKind::Let, 0, origin } };
    CoreStmt receive;
    receive.kind = CoreStmtKind::Let; receive.var = 0; receive.expr = call(1); receive.org = origin;
    entry.body.stmts.push_back(std::move(receive));
    CoreStmt print;
    print.kind = CoreStmtKind::Print; print.org = origin;
    CorePrintArg shown; shown.kind = CorePrintArg::View; shown.view = make_unique<CoreView>();
    shown.view->place = make_unique<CorePlace>(); print.print.push_back(std::move(shown));
    entry.body.stmts.push_back(std::move(print)); entry.summary.outputs = true;
    CoreImpl outer;
    outer.name = "outer"; outer.body.scope = 0;
    outer.results = { CoreResultDescriptor { bytes, CoreRequest::Value } };
    outer.summary.constructs = { 0 }; outer.body.value = call(2);
    if (!sameIdentity) {
        outer.results[0].namedLocal = 0;
        outer.vars = { CoreVar { "named", bytes, CoreVarKind::Var, 0, origin } };
        CoreStmt seed;
        seed.kind = CoreStmtKind::Let; seed.var = 0; seed.org = origin;
        seed.expr = make_unique<CoreExpr>(); seed.expr->kind = CoreExprKind::Bytes;
        seed.expr->type = bytes; seed.expr->bytes = { 65 }; seed.expr->org = origin;
        outer.body.stmts.push_back(std::move(seed));
        CoreStmt fallback;
        fallback.kind = CoreStmtKind::If;
        fallback.org = origin;
        fallback.expr = make_unique<CoreExpr>();
        fallback.expr->kind = CoreExprKind::Bool;
        fallback.expr->type = core.BoolType();
        fallback.expr->flag = false;
        fallback.then = make_unique<CoreBlock>();
        fallback.then->scope = 1;
        CoreStmt returned;
        returned.kind = CoreStmtKind::RetValues;
        returned.org = origin;
        returned.values.push_back(named());
        fallback.then->stmts.push_back(std::move(returned));
        outer.body.stmts.push_back(std::move(fallback));
    }
    CoreImpl helper;
    helper.name = "helper"; helper.body.scope = 0;
    helper.results = { CoreResultDescriptor { bytes, CoreRequest::Value, 0 } };
    helper.vars = { CoreVar { "named", bytes, CoreVarKind::Var, 0, origin } };
    helper.summary.constructs = { 0 }; helper.summary.needs = { 0 }; helper.summary.escapes = { 0 };
    CoreStmt initial;
    initial.kind = CoreStmtKind::Let; initial.var = 0; initial.org = origin;
    initial.expr = make_unique<CoreExpr>(); initial.expr->kind = CoreExprKind::Bytes;
    initial.expr->type = bytes; initial.expr->bytes = { (uint8_t)(sameIdentity ? 65 : 66) }; initial.expr->org = origin;
    helper.body.stmts.push_back(std::move(initial));
    CoreStmt branch;
    branch.kind = CoreStmtKind::If; branch.org = origin;
    branch.expr = make_unique<CoreExpr>(); branch.expr->kind = CoreExprKind::Bool;
    branch.expr->type = core.BoolType(); branch.expr->flag = true;
    branch.then = make_unique<CoreBlock>(); branch.then->scope = 1;
    CoreStmt escaping;
    escaping.kind = CoreStmtKind::ReturnFrom; escaping.target = 0; escaping.org = origin; escaping.values.push_back(named());
    branch.then->stmts.push_back(std::move(escaping)); helper.body.stmts.push_back(std::move(branch));
    CoreStmt returned;
    returned.kind = CoreStmtKind::RetValues; returned.org = origin; returned.values.push_back(named());
    helper.body.stmts.push_back(std::move(returned));
    core.impls.push_back(std::move(entry)); core.impls.push_back(std::move(outer)); core.impls.push_back(std::move(helper));
    core.contexts = { CoreContext { .impl = 0 }, CoreContext { .impl = 1, .resultroots = { {} } }, CoreContext { .impl = 2, .resultroots = { {} } } };
    core.targets = { CoreTargetSet { { 1 } } };
    return core;
}

CoreModule DeferredTargetCleanup(bool own = false) {
    auto core = InterruptedReturn(CoreStmtKind::Break);
    auto u8 = core.IntType(CoreIntTy::U8);
    auto bytes = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = u8 });
    core.files = { "deferred-target-cleanup.goose" };
    core.impls[0].summary.unknown = false;
    core.impls[0].summary.outputs = true;
    auto call = [&](int context) {
        auto expression = make_unique<CoreExpr>();
        expression->kind = CoreExprKind::Call;
        expression->ctx = context;
        expression->type = u8;
        expression->org = origin;
        return expression;
    };
    auto &producer = core.impls[1];
    producer.vars.clear();
    producer.body.stmts.clear();
    producer.body.value = make_unique<CoreExpr>();
    producer.body.value->kind = CoreExprKind::Arr;
    producer.body.value->type = bytes;
    producer.body.value->org = origin;
    producer.body.value->elems.push_back(Integer(u8, "65"));
    if (own) {
        producer.vars = { {"local", bytes, CoreVarKind::Var, 1, origin} };
        auto operand = make_unique<CoreExpr>();
        operand->kind = CoreExprKind::Block;
        operand->type = u8;
        operand->org = origin;
        operand->then = make_unique<CoreBlock>();
        operand->then->scope = 1;
        CoreStmt initial;
        initial.kind = CoreStmtKind::Let;
        initial.var = 0;
        initial.org = origin;
        initial.expr = make_unique<CoreExpr>();
        initial.expr->kind = CoreExprKind::Arr;
        initial.expr->type = bytes;
        initial.expr->org = origin;
        initial.expr->elems.push_back(Integer(u8, "70"));
        auto inner = make_unique<CoreExpr>();
        inner->kind = CoreExprKind::Block;
        inner->type = u8;
        inner->org = origin;
        inner->then = make_unique<CoreBlock>();
        inner->then->scope = 2;
        CoreStmt returned;
        returned.kind = CoreStmtKind::RetValues;
        returned.org = origin;
        returned.values.push_back(Bytes(bytes, 66));
        inner->then->stmts.push_back(std::move(returned));
        inner->then->value = Integer(u8, "0");
        initial.expr->elems.push_back(std::move(inner));
        operand->then->stmts.push_back(std::move(initial));
        operand->then->value = Integer(u8, "67");
        producer.body.value->elems.push_back(std::move(operand));
        return core;
    }
    producer.body.value->elems.push_back(call(2));
    CoreImpl middle;
    middle.name = "middle";
    middle.body.scope = 0;
    middle.results = { {u8, CoreRequest::Register} };
    middle.vars = { {"local", bytes, CoreVarKind::Var, 0, origin} };
    middle.summary.needs = {0};
    middle.summary.escapes = {0};
    CoreStmt initial;
    initial.kind = CoreStmtKind::Let;
    initial.var = 0;
    initial.org = origin;
    initial.expr = make_unique<CoreExpr>();
    initial.expr->kind = CoreExprKind::Arr;
    initial.expr->type = bytes;
    initial.expr->org = origin;
    initial.expr->elems.push_back(Integer(u8, "70"));
    initial.expr->elems.push_back(call(3));
    middle.body.stmts.push_back(std::move(initial));
    middle.body.value = Integer(u8, "67");
    CoreImpl helper;
    helper.name = "exit";
    helper.body.scope = 0;
    helper.results = { {u8, CoreRequest::Register} };
    helper.summary.needs = {0};
    helper.summary.escapes = {0};
    CoreStmt exit;
    exit.kind = CoreStmtKind::ReturnFrom;
    exit.target = 0;
    exit.org = origin;
    exit.values.push_back(Bytes(bytes, 66));
    helper.body.stmts.push_back(std::move(exit));
    helper.body.value = Integer(u8, "0");
    core.impls.push_back(std::move(middle));
    core.impls.push_back(std::move(helper));
    core.contexts = { CoreContext { .impl = 0 }, CoreContext { .impl = 1, .resultroots = { {} } },
        CoreContext { .impl = 2, .resultroots = { {} } }, CoreContext { .impl = 3, .resultroots = { {} } } };
    core.targets = { CoreTargetSet { {1} } };
    return core;
}

CoreModule DeferredValueBreakCleanup() {
    auto core = InterruptedReturn(CoreStmtKind::Break);
    auto u8 = core.IntType(CoreIntTy::U8);
    auto bytes = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = u8 });
    core.files = { "deferred-value-break.goose" };
    auto branch = [&](int left, int right) {
        auto value = make_unique<CoreExpr>();
        value->kind = CoreExprKind::If;
        value->type = u8;
        value->org = origin;
        value->a = make_unique<CoreExpr>();
        value->a->kind = CoreExprKind::Bool;
        value->a->type = core.BoolType();
        value->a->flag = true;
        value->then = make_unique<CoreBlock>();
        value->then->scope = left;
        value->then->value = Integer(u8, "0");
        value->otherwise = make_unique<CoreBlock>();
        value->otherwise->scope = right;
        value->otherwise->value = Integer(u8, "0");
        return value;
    };
    auto &producer = core.impls[1];
    producer.vars = { {"local", bytes, CoreVarKind::Var, 2, origin} };
    producer.body.stmts.clear();
    producer.body.value = make_unique<CoreExpr>();
    producer.body.value->kind = CoreExprKind::Block;
    producer.body.value->type = bytes;
    producer.body.value->org = origin;
    producer.body.value->then = make_unique<CoreBlock>();
    producer.body.value->then->scope = 1;
    auto array = make_unique<CoreExpr>();
    array->kind = CoreExprKind::Arr;
    array->type = bytes;
    array->org = origin;
    array->elems.push_back(Integer(u8, "65"));
    auto outer = branch(2, 5);
    CoreStmt initial;
    initial.kind = CoreStmtKind::Let;
    initial.var = 0;
    initial.org = origin;
    initial.expr = make_unique<CoreExpr>();
    initial.expr->kind = CoreExprKind::Arr;
    initial.expr->type = bytes;
    initial.expr->org = origin;
    initial.expr->elems.push_back(Integer(u8, "70"));
    auto inner = branch(3, 4);
    CoreStmt broken;
    broken.kind = CoreStmtKind::BreakValue;
    broken.org = origin;
    broken.expr = Bytes(bytes, 66);
    inner->then->stmts.push_back(std::move(broken));
    initial.expr->elems.push_back(std::move(inner));
    outer->then->stmts.push_back(std::move(initial));
    array->elems.push_back(std::move(outer));
    producer.body.value->then->value = std::move(array);
    return core;
}

CoreModule Fixture(string_view name) {
    if (name == "nested-break") return InterruptedReturn(CoreStmtKind::Break, true);
    if (name == "nested-continue") return InterruptedReturn(CoreStmtKind::Continue, true);
    if (name == "value-break-cleanup") return DeferredValueBreakCleanup();
    if (name == "own-deferred-cleanup") return DeferredTargetCleanup(true);
    if (name == "deferred-cleanup") return DeferredTargetCleanup();
    if (name == "cross-same") return CrossActivationNamed(true);
    if (name == "cross-different") return CrossActivationNamed(false);
    if (name == "owner-child") return InterruptedOwnerChild(false);
    if (name == "owner-named") return InterruptedOwnerChild(true);
    if (name == "call") return InterruptedCall();
    if (name == "named-borrow") return NamedBorrowGrowth();
    assert(name == "break" || name == "continue");
    return InterruptedReturn(name == "continue" ? CoreStmtKind::Continue : CoreStmtKind::Break);
}

void Valid(GirModule module) {
    auto violation = GirVerifier(module).Verify();
    if (violation) fprintf(stderr, "%s: %s\n", violation->code.c_str(), violation->message.c_str());
    assert(!violation);
}

}

int main(int argc, char **argv) try {
    if (argc == 3) {
        auto core = Fixture(argv[1]);
        auto high = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
        Valid(high);
        auto low = GirToLow(high).Lower();
        Valid(low);
        auto trace = string_view(argv[2]) == "-" ? nullopt : optional<string>(argv[2]);
        auto emitted = GirCEmitter(low, trace).Emit();
        for (const auto *section : { "runtime.h", "runtime_impl.h", "runtime_threads.h" })
            for (const auto &file : runtime_files)
                if (string_view(file.name) == section) printf("%.*s\n", (int)file.text.size(), file.text.data());
        printf("%s\n%s", emitted.head.c_str(), emitted.result.c_str());
        return 0;
    }
    if (argc == 2 && string_view(argv[1]) == "runtime") {
        auto core = Fixture("deferred-cleanup");
        auto high = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
        Valid(high);
        auto low = GirToLow(high).Lower();
        Valid(low);
        auto emitted = GirCEmitter(low).Emit();
        for (const auto *section : { "runtime.h", "runtime_impl.h", "runtime_threads.h" })
            for (const auto &file : runtime_files)
                if (string_view(file.name) == section) printf("%.*s\n", (int)file.text.size(), file.text.data());
        printf("%s\n%s", emitted.head.c_str(), emitted.unit.data.c_str());
        return 0;
    }
    if (argc == 2) {
        auto core = Fixture(argv[1]);
        printf("%s\n", CoreWriter(core).Write().c_str());
        return 0;
    }
    assert(argc == 1);
    for (auto name : { "break", "continue", "call", "named-borrow", "owner-child", "owner-named", "cross-same", "cross-different", "deferred-cleanup", "own-deferred-cleanup", "value-break-cleanup", "nested-break", "nested-continue" }) {
        auto core = Fixture(name);
        auto high = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
        Valid(high);
        Valid(GirToLow(high).Lower());
    }
    printf("compiler_gir_reservations ok\n");
} catch (const CompileError &error) {
    fprintf(stderr, "%s\n", error.msg.c_str());
    return 1;
}
