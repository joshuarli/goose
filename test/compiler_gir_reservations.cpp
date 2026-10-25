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

CoreModule BorrowedWaiting(CoreStmtKind interruption) {
    auto core = InterruptedReturn(interruption);
    core.files = {"borrowed-waiting.goose"};
    auto &producer = core.impls[1];
    auto bytes = producer.results[0].type;
    producer.vars[0].scope = 2;
    auto loop = std::move(producer.body.stmts[0]);
    loop.then->scope = 2;
    auto &broken = loop.then->stmts[0];
    broken.kind = CoreStmtKind::BreakValue;
    broken.expr = std::move(broken.values[0]);
    broken.values.clear();
    broken.expr->elems[1]->then->scope = 3;
    producer.body.stmts.clear();
    producer.body.value = make_unique<CoreExpr>();
    producer.body.value->kind = CoreExprKind::Block;
    producer.body.value->type = bytes;
    producer.body.value->org = origin;
    producer.body.value->then = make_unique<CoreBlock>();
    producer.body.value->then->scope = 1;
    producer.body.value->then->stmts.push_back(std::move(loop));
    producer.body.value->then->value = Bytes(bytes, 67);
    return core;
}

CoreModule BorrowedWaitingChild(CoreStmtKind interruption) {
    auto core = BorrowedWaiting(interruption);
    auto &producer = core.impls[1];
    auto outer = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = producer.results[0].type });
    producer.results[0].type = outer;
    producer.summary.aborts = true;
    auto child = std::move(producer.body.value);
    producer.body.value = make_unique<CoreExpr>();
    producer.body.value->kind = CoreExprKind::Arr;
    producer.body.value->type = outer;
    producer.body.value->org = origin;
    producer.body.value->elems.push_back(std::move(child));
    core.impls[0].vars[0].type = outer;
    core.impls[0].body.stmts[0].expr->type = outer;
    return core;
}

CoreModule BorrowedWaitingNamed(CoreStmtKind interruption) {
    auto core = BorrowedWaiting(interruption);
    auto &producer = core.impls[1];
    auto array = producer.results[0].type;
    producer.vars.insert(producer.vars.begin(), CoreVar {"named", array, CoreVarKind::Var, 0, origin});
    producer.results[0].namedLocal = 0;
    CoreStmt initialized;
    initialized.kind = CoreStmtKind::Let;
    initialized.var = 0;
    initialized.org = origin;
    initialized.expr = Bytes(array, 65);
    producer.body.stmts.push_back(std::move(initialized));
    auto &loop = producer.body.value->then->stmts[0];
    loop.var = 1;
    loop.then->stmts[0].expr->elems[0]->value = "66";
    auto &tail = producer.body.value->then->value;
    tail = make_unique<CoreExpr>();
    tail->kind = CoreExprKind::ResultLocal;
    tail->var = 0;
    tail->type = array;
    tail->org = origin;
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

CoreModule WaitingCompletion(bool explicitReturn) {
    CoreModule core;
    core.profile = CoreProfile::Construction;
    core.files = { "tail-completion-siblings.goose" };
    auto u8 = core.IntType(CoreIntTy::U8);
    auto bytes = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = u8 });
    CoreImpl entry;
    entry.name = "entry";
    entry.body.scope = 0;
    entry.vars = { {"first", bytes, CoreVarKind::Let, 0, origin}, {"second", bytes, CoreVarKind::Let, 0, origin} };
    entry.summary.aborts = true;
    entry.summary.outputs = true;
    CoreStmt receive;
    receive.kind = CoreStmtKind::Receive;
    receive.vars = { 0, 1 };
    receive.org = origin;
    receive.expr = make_unique<CoreExpr>();
    receive.expr->kind = CoreExprKind::Call;
    receive.expr->ctx = 1;
    receive.expr->org = origin;
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
    producer.results = { {bytes, CoreRequest::Value}, {bytes, CoreRequest::Value} };
    producer.summary.constructs = { 0, 1 };
    producer.summary.needs = { 0 };
    producer.summary.escapes = { 0 };
    producer.summary.aborts = true;
    CoreStmt unreachable;
    unreachable.kind = CoreStmtKind::If;
    unreachable.org = origin;
    unreachable.expr = make_unique<CoreExpr>();
    unreachable.expr->kind = CoreExprKind::Bool;
    unreachable.then = make_unique<CoreBlock>();
    unreachable.then->scope = 1;
    CoreStmt fallback;
    fallback.kind = CoreStmtKind::RetValues;
    fallback.org = origin;
    fallback.values.push_back(Bytes(bytes, 70));
    fallback.values.push_back(Bytes(bytes, 68));
    unreachable.then->stmts.push_back(std::move(fallback));
    producer.body.stmts.push_back(std::move(unreachable));
    auto first = make_unique<CoreExpr>();
    first->kind = CoreExprKind::Block;
    first->type = bytes;
    first->org = origin;
    first->then = make_unique<CoreBlock>();
    first->then->scope = 2;
    auto array = make_unique<CoreExpr>();
    array->kind = CoreExprKind::Arr;
    array->type = bytes;
    array->org = origin;
    array->elems.push_back(Integer(u8, "66"));
    auto branch = make_unique<CoreExpr>();
    branch->kind = CoreExprKind::If;
    branch->type = u8;
    branch->org = origin;
    branch->a = make_unique<CoreExpr>();
    branch->a->kind = CoreExprKind::Bool;
    branch->a->flag = true;
    branch->then = make_unique<CoreBlock>();
    branch->then->scope = 3;
    CoreStmt broken;
    broken.kind = CoreStmtKind::BreakValue;
    broken.org = origin;
    broken.expr = Bytes(bytes, 67);
    branch->then->stmts.push_back(std::move(broken));
    branch->then->value = Integer(u8, "68");
    branch->otherwise = make_unique<CoreBlock>();
    branch->otherwise->scope = 4;
    branch->otherwise->value = Integer(u8, "69");
    array->elems.push_back(std::move(branch));
    first->then->value = std::move(array);
    auto second = make_unique<CoreExpr>();
    second->kind = CoreExprKind::Block;
    second->type = bytes;
    second->org = origin;
    second->then = make_unique<CoreBlock>();
    second->then->scope = 5;
    CoreStmt escape;
    escape.kind = CoreStmtKind::ReturnFrom;
    escape.target = 0;
    escape.org = origin;
    second->then->stmts.push_back(std::move(escape));
    second->then->value = Bytes(bytes, 69);
    if (explicitReturn) {
        CoreStmt returned;
        returned.kind = CoreStmtKind::RetValues;
        returned.org = origin;
        returned.values.push_back(std::move(first));
        returned.values.push_back(std::move(second));
        producer.body.stmts.push_back(std::move(returned));
    } else {
        producer.body.value = make_unique<CoreExpr>();
        producer.body.value->kind = CoreExprKind::Values;
        producer.body.value->values.push_back(std::move(first));
        producer.body.value->values.push_back(std::move(second));
    }
    core.impls.push_back(std::move(entry));
    core.impls.push_back(std::move(producer));
    core.targets = { CoreTargetSet { {0} } };
    core.contexts = { CoreContext { .impl = 0 }, CoreContext { .impl = 1, .resultroots = {{}, {}} } };
    return core;
}

CoreModule WaitingArgument(bool guarded) {
    auto core = InterruptedReturn(CoreStmtKind::Break);
    auto bytes = core.impls[1].results[0].type;
    auto i64 = core.IntType(CoreIntTy::I64);
    auto &entry = core.impls[0];
    entry.summary = {};
    entry.body.stmts.resize(1);
    if (!guarded) {
        entry.vars.push_back(CoreVar { "second", bytes, CoreVarKind::Var, 0, origin });
        entry.body.stmts[0].kind = CoreStmtKind::Receive;
        entry.body.stmts[0].vars = {0, 1};
    }
    auto &producer = core.impls[1];
    producer.vars = { CoreVar { "argument", i64, CoreVarKind::Let, 0, origin } };
    producer.params = {{0, false}};
    producer.body = CoreBlock {};
    producer.body.scope = 0;
    producer.body.value = make_unique<CoreExpr>();
    producer.body.value->kind = CoreExprKind::Block;
    producer.body.value->type = bytes;
    producer.body.value->org = origin;
    producer.body.value->then = make_unique<CoreBlock>();
    producer.body.value->then->scope = 1;
    CoreStmt escaped;
    escaped.kind = CoreStmtKind::ReturnFrom;
    escaped.target = 0;
    escaped.org = origin;
    producer.body.value->then->stmts.push_back(std::move(escaped));
    producer.body.value->then->value = Bytes(bytes, 66);
    producer.summary.needs = {0};
    producer.summary.escapes = {0};
    if (!guarded) {
        producer.results.push_back({bytes, CoreRequest::Value});
        producer.summary.constructs.push_back(1);
        core.contexts[1].resultroots.push_back({});
        auto first = std::move(producer.body.value->then->value);
        producer.body.value->then->value = make_unique<CoreExpr>();
        producer.body.value->then->value->kind = CoreExprKind::Values;
        producer.body.value->then->value->values.push_back(std::move(first));
        producer.body.value->then->value->values.push_back(Bytes(bytes, 67));
    }
    auto argument = make_unique<CoreExpr>();
    argument->kind = CoreExprKind::Block;
    argument->type = i64;
    argument->org = origin;
    argument->then = make_unique<CoreBlock>();
    argument->then->scope = 1;
    CoreStmt interrupted;
    interrupted.kind = CoreStmtKind::ReturnFrom;
    interrupted.target = 0;
    interrupted.org = origin;
    argument->then->stmts.push_back(std::move(interrupted));
    argument->then->value = Integer(i64, "0");
    entry.body.stmts[0].expr->args.push_back(CoreArgValue {std::move(argument)});
    core.targets = { CoreTargetSet {{0}} };
    return core;
}

enum class AdaptedCase { Open, Built, Nested };

CoreModule AdaptedCall(AdaptedCase mode) {
    bool built = mode == AdaptedCase::Built;
    bool nested = mode == AdaptedCase::Nested;
    CoreModule core;
    core.profile = CoreProfile::Construction;
    core.files = { "adapted-call.goose" };
    auto u8 = core.IntType(CoreIntTy::U8);
    auto bytes = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = u8 });
    auto element = nested ? bytes : u8;
    auto producerType = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = element });
    auto receivingType = core.Intern(CoreType { .kind = CoreType::Grow, .elem = element });
    CoreImpl entry;
    entry.name = "entry";
    entry.body.scope = 0;
    entry.vars = { CoreVar { "output", receivingType, CoreVarKind::Var, 0, origin } };
    entry.summary.aborts = true;
    entry.summary.outputs = true;
    CoreStmt received;
    received.kind = CoreStmtKind::Let;
    received.var = 0;
    received.org = origin;
    received.expr = make_unique<CoreExpr>();
    received.expr->kind = CoreExprKind::Call;
    received.expr->type = receivingType;
    received.expr->ctx = 1;
    received.expr->org = origin;
    entry.body.stmts.push_back(std::move(received));
    CoreStmt printed;
    printed.kind = CoreStmtKind::Print;
    printed.org = origin;
    CorePrintArg viewed;
    viewed.kind = CorePrintArg::View;
    viewed.view = make_unique<CoreView>();
    viewed.view->place = make_unique<CorePlace>();
    viewed.view->place->index = 0;
    printed.print.push_back(std::move(viewed));
    entry.body.stmts.push_back(std::move(printed));
    CoreImpl receiver;
    receiver.name = "receiver";
    receiver.body.scope = 0;
    receiver.results = {{receivingType, CoreRequest::Value}};
    receiver.summary.constructs = {0};
    receiver.summary.aborts = true;
    receiver.body.value = make_unique<CoreExpr>();
    receiver.body.value->kind = CoreExprKind::Call;
    receiver.body.value->type = producerType;
    receiver.body.value->ctx = 2;
    receiver.body.value->org = origin;
    CoreImpl producer;
    producer.name = "producer";
    producer.body.scope = 0;
    producer.results = {{producerType, CoreRequest::Value}};
    producer.summary.constructs = {0};
    producer.summary.aborts = true;
    if (nested) {
        producer.body.value = make_unique<CoreExpr>();
        producer.body.value->kind = CoreExprKind::Arr;
        producer.body.value->type = producerType;
        producer.body.value->org = origin;
        producer.body.value->elems.push_back(Bytes(bytes, 65));
        auto second = Bytes(bytes, 66);
        second->bytes.push_back(67);
        producer.body.value->elems.push_back(std::move(second));
    } else {
        producer.summary.needs = {0};
        producer.summary.escapes = {0};
        if (built) {
            producer.results[0].namedLocal = 0;
            producer.vars = { CoreVar { "named", producerType, CoreVarKind::Var, 0, origin } };
            CoreStmt initialized;
            initialized.kind = CoreStmtKind::Let;
            initialized.var = 0;
            initialized.org = origin;
            initialized.expr = Bytes(producerType, 70);
            producer.body.stmts.push_back(std::move(initialized));
        }
        producer.body.value = make_unique<CoreExpr>();
        producer.body.value->kind = CoreExprKind::Block;
        producer.body.value->type = producerType;
        producer.body.value->org = origin;
        producer.body.value->then = make_unique<CoreBlock>();
        producer.body.value->then->scope = 1;
        CoreStmt escaped;
        escaped.kind = CoreStmtKind::ReturnFrom;
        escaped.target = 0;
        escaped.org = origin;
        auto value = make_unique<CoreExpr>();
        value->kind = CoreExprKind::Arr;
        value->type = receivingType;
        value->org = origin;
        value->elems.push_back(Integer(u8, "65"));
        escaped.values.push_back(std::move(value));
        producer.body.value->then->stmts.push_back(std::move(escaped));
        if (built) {
            producer.body.value->then->value = make_unique<CoreExpr>();
            producer.body.value->then->value->kind = CoreExprKind::ResultLocal;
            producer.body.value->then->value->var = 0;
            producer.body.value->then->value->type = producerType;
            producer.body.value->then->value->org = origin;
        } else producer.body.value->then->value = Bytes(producerType, 66);
    }
    core.impls.push_back(std::move(entry));
    core.impls.push_back(std::move(receiver));
    core.impls.push_back(std::move(producer));
    core.contexts = { CoreContext { .impl = 0 }, CoreContext { .impl = 1, .resultroots = {{}} }, CoreContext { .impl = 2, .resultroots = {{}} } };
    if (!nested) core.targets = { CoreTargetSet {{1}} };
    return core;
}

CoreModule NamedLayout(bool packedLocal) {
    auto core = AdaptedCall(AdaptedCase::Open);
    core.impls.resize(2);
    core.contexts.resize(2);
    core.targets.clear();
    auto u8 = core.IntType(CoreIntTy::U8);
    auto packed = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = u8 });
    auto grow = core.Intern(CoreType { .kind = CoreType::Grow, .elem = u8 });
    auto localType = packedLocal ? packed : grow;
    auto resultType = packedLocal ? grow : packed;
    auto &entry = core.impls[0];
    entry.vars[0].type = resultType;
    entry.body.stmts[0].expr->type = resultType;
    auto &producer = core.impls[1];
    producer.results = {{resultType, CoreRequest::Value, 0}};
    producer.vars = {CoreVar {"named", localType, CoreVarKind::Var, 0, origin}};
    producer.body.value.reset();
    CoreStmt initialized;
    initialized.kind = CoreStmtKind::Let;
    initialized.var = 0;
    initialized.org = origin;
    if (packedLocal) initialized.expr = Bytes(localType, 65);
    else {
        initialized.expr = make_unique<CoreExpr>();
        initialized.expr->kind = CoreExprKind::Arr;
        initialized.expr->type = localType;
        initialized.expr->org = origin;
        initialized.expr->elems.push_back(Integer(u8, "65"));
    }
    producer.body.stmts.push_back(std::move(initialized));
    producer.body.value = make_unique<CoreExpr>();
    producer.body.value->kind = CoreExprKind::ResultLocal;
    producer.body.value->var = 0;
    producer.body.value->type = localType;
    producer.body.value->org = origin;
    return core;
}

CoreModule NamedNestedRead() {
    auto core = NamedLayout(true);
    auto packed = core.impls[1].vars[0].type;
    core.impls[1].results[0].type = packed;
    core.impls[0].body.stmts[0].expr->type = packed;
    auto &initialized = core.impls[1].body.stmts[0];
    initialized.expr = make_unique<CoreExpr>();
    initialized.expr->kind = CoreExprKind::Call;
    initialized.expr->type = packed;
    initialized.expr->ctx = 2;
    initialized.expr->org = origin;
    CoreStmt printed;
    printed.kind = CoreStmtKind::Print;
    printed.org = origin;
    CorePrintArg viewed;
    viewed.kind = CorePrintArg::View;
    viewed.view = make_unique<CoreView>();
    viewed.view->place = make_unique<CorePlace>();
    printed.print.push_back(std::move(viewed));
    core.impls[1].body.stmts.push_back(std::move(printed));
    core.impls[1].summary.outputs = true;
    CoreImpl helper;
    helper.name = "initialize_named";
    helper.body.scope = 0;
    helper.results = {{packed, CoreRequest::Value}};
    helper.summary.constructs = {0};
    helper.summary.aborts = true;
    helper.body.value = Bytes(packed, 65);
    core.impls.push_back(std::move(helper));
    core.contexts.push_back(CoreContext {.impl = 2, .resultroots = {{}}});
    return core;
}

CoreModule NamedHelperRead() {
    auto core = NamedNestedRead();
    auto packed = core.impls[1].vars[0].type;
    auto reference = core.Intern(CoreType { .kind = CoreType::Ref, .mut = CoreMut::Const, .elem = packed });
    auto unit = core.Intern(CoreType { .kind = CoreType::Unit });
    CoreImpl helper;
    helper.name = "read_named";
    helper.body.scope = 0;
    helper.vars = {{"value", reference, CoreVarKind::Let, 0, origin}};
    helper.params = {{0, true}};
    helper.summary.outputs = true;
    helper.summary.reads = {{false, 0}};
    CoreStmt printed;
    printed.kind = CoreStmtKind::Print;
    printed.org = origin;
    CorePrintArg viewed;
    viewed.kind = CorePrintArg::View;
    viewed.view = make_unique<CoreView>();
    viewed.view->place = make_unique<CorePlace>();
    viewed.view->place->kind = CorePlace::Deref;
    viewed.view->place->expr = make_unique<CoreExpr>();
    viewed.view->place->expr->kind = CoreExprKind::Read;
    viewed.view->place->expr->type = reference;
    viewed.view->place->expr->place = make_unique<CorePlace>();
    printed.print.push_back(std::move(viewed));
    helper.body.stmts.push_back(std::move(printed));
    core.impls.push_back(std::move(helper));
    CoreContext context;
    context.impl = 3;
    context.varroots = {{0, {{CoreRootRef::Param, 0}}}};
    core.contexts.push_back(std::move(context));
    auto &called = core.impls[1].body.stmts[1];
    called = CoreStmt {};
    called.kind = CoreStmtKind::Expr;
    called.org = origin;
    called.expr = make_unique<CoreExpr>();
    called.expr->kind = CoreExprKind::Call;
    called.expr->type = unit;
    called.expr->ctx = 3;
    called.expr->org = origin;
    CoreArgReference argument;
    argument.mut = CoreMut::Const;
    argument.place = make_unique<CorePlace>();
    called.expr->args.push_back(std::move(argument));
    return core;
}

CoreModule WaitingAfterNamedValue() {
    auto core = NamedLayout(true);
    auto &producer = core.impls[1];
    auto packed = producer.vars[0].type;
    producer.results[0].type = packed;
    core.impls[0].vars[0].type = packed;
    core.impls[0].body.stmts[0].expr->type = packed;
    auto named = std::move(producer.body.value);
    producer.body.value = make_unique<CoreExpr>();
    producer.body.value->kind = CoreExprKind::Block;
    producer.body.value->type = packed;
    producer.body.value->org = origin;
    producer.body.value->then = make_unique<CoreBlock>();
    producer.body.value->then->scope = 1;
    CoreStmt returned;
    returned.kind = CoreStmtKind::RetValues;
    returned.org = origin;
    returned.values.push_back(Bytes(packed, 66));
    producer.body.value->then->stmts.push_back(std::move(returned));
    producer.body.value->then->value = std::move(named);
    return core;
}

CoreModule FixedCallIntoLimited(int64_t capacity) {
    CoreModule core;
    core.profile = CoreProfile::Construction;
    core.files = { "fixed-call-delivery.goose" };
    auto u8 = core.IntType(CoreIntTy::U8);
    auto fixed = core.Intern(CoreType { .kind = CoreType::Arr, .elem = u8, .count = 2 });
    auto limited = core.Intern(CoreType { .kind = CoreType::Limited, .elem = u8, .count = capacity });
    CoreImpl entry;
    entry.name = "entry";
    entry.body.scope = 0;
    entry.summary.unknown = true;
    entry.vars = { CoreVar { "owner", limited, CoreVarKind::Var, 0, origin } };
    CoreStmt initialized;
    initialized.kind = CoreStmtKind::Let;
    initialized.var = 0;
    initialized.org = origin;
    initialized.expr = make_unique<CoreExpr>();
    initialized.expr->kind = CoreExprKind::Call;
    initialized.expr->type = fixed;
    initialized.expr->ctx = 1;
    initialized.expr->org = origin;
    entry.body.stmts.push_back(std::move(initialized));
    CorePrintArg delivered;
    delivered.kind = CorePrintArg::View;
    delivered.view = make_unique<CoreView>();
    delivered.view->place = make_unique<CorePlace>();
    delivered.view->place->index = 0;
    CoreStmt inspect;
    inspect.kind = CoreStmtKind::Print;
    inspect.org = origin;
    inspect.print.push_back(std::move(delivered));
    entry.body.stmts.push_back(std::move(inspect));
    CoreImpl producer;
    producer.name = "producer";
    producer.body.scope = 0;
    producer.summary.outputs = true;
    producer.results = { CoreResultDescriptor { fixed, CoreRequest::Register } };
    CoreStmt effect;
    effect.kind = CoreStmtKind::Print;
    effect.org = origin;
    effect.print.push_back(CorePrintArg { .kind = CorePrintArg::Text, .str = "effect" });
    producer.body.stmts.push_back(std::move(effect));
    producer.body.value = make_unique<CoreExpr>();
    producer.body.value->kind = CoreExprKind::Arr;
    producer.body.value->type = fixed;
    producer.body.value->org = origin;
    producer.body.value->elems.push_back(Integer(u8, "65"));
    producer.body.value->elems.push_back(Integer(u8, "66"));
    core.impls.push_back(std::move(entry));
    core.impls.push_back(std::move(producer));
    core.contexts = { CoreContext { .impl = 0 }, CoreContext { .impl = 1, .resultroots = { {} } } };
    return core;
}

CoreModule EscapingDeliveryBranch(bool variableLive) {
    auto core = FixedCallIntoLimited(3);
    core.files = { "escaping-delivery.goose" };
    auto u8 = core.IntType(CoreIntTy::U8);
    auto fixed = core.Intern(CoreType { .kind = CoreType::Arr, .elem = u8, .count = 2 });
    auto variable = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = u8 });
    auto array = [&](CoreTypeId type, bool third) {
        auto value = make_unique<CoreExpr>();
        value->kind = CoreExprKind::Arr;
        value->type = type;
        value->org = origin;
        value->elems.push_back(Integer(u8, "65"));
        value->elems.push_back(Integer(u8, "66"));
        if (third) value->elems.push_back(Integer(u8, "67"));
        return value;
    };
    auto expression = make_unique<CoreExpr>();
    expression->kind = CoreExprKind::If;
    expression->type = variableLive ? variable : fixed;
    expression->org = origin;
    expression->a = make_unique<CoreExpr>();
    expression->a->kind = CoreExprKind::Bool;
    expression->a->type = core.Intern(CoreType { .kind = CoreType::Bool });
    expression->a->flag = false;
    expression->then = make_unique<CoreBlock>();
    expression->then->scope = 1;
    CoreStmt aborted;
    aborted.kind = CoreStmtKind::Abort;
    aborted.message = "dead";
    aborted.org = origin;
    expression->then->stmts.push_back(std::move(aborted));
    expression->then->value = array(variableLive ? fixed : variable, !variableLive);
    expression->otherwise = make_unique<CoreBlock>();
    expression->otherwise->scope = 2;
    expression->otherwise->value = array(variableLive ? variable : fixed, variableLive);
    core.impls[0].body.stmts[0].expr = std::move(expression);
    return core;
}

CoreModule LowFuelBlockValue() {
    auto core = FixedCallIntoLimited(1);
    core.files = { "query-fuel.goose" };
    core.impls.resize(1);
    core.contexts.resize(1);
    auto u8 = core.IntType(CoreIntTy::U8);
    auto i64 = core.IntType(CoreIntTy::I64);
    auto fixed = core.Intern(CoreType { .kind = CoreType::Arr, .elem = u8, .count = 1 });
    auto variable = core.Intern(CoreType { .kind = CoreType::VarArr, .elem = u8 });
    auto conditional = make_unique<CoreExpr>();
    conditional->kind = CoreExprKind::If;
    conditional->type = fixed;
    conditional->org = origin;
    conditional->a = make_unique<CoreExpr>();
    conditional->a->kind = CoreExprKind::Bool;
    conditional->a->type = core.Intern(CoreType { .kind = CoreType::Bool });
    conditional->a->flag = false;
    conditional->then = make_unique<CoreBlock>();
    conditional->then->scope = 2;
    for (int index = 0; index < 80; index++) {
        CoreStmt ignored;
        ignored.kind = CoreStmtKind::Expr;
        ignored.org = origin;
        ignored.expr = Integer(i64, "0");
        conditional->then->stmts.push_back(std::move(ignored));
    }
    CoreStmt aborted;
    aborted.kind = CoreStmtKind::Abort;
    aborted.message = "dead";
    aborted.org = origin;
    conditional->then->stmts.push_back(std::move(aborted));
    conditional->then->value = make_unique<CoreExpr>();
    conditional->then->value->kind = CoreExprKind::Arr;
    conditional->then->value->type = variable;
    conditional->then->value->org = origin;
    conditional->then->value->elems.push_back(Integer(u8, "9"));
    conditional->otherwise = make_unique<CoreBlock>();
    conditional->otherwise->scope = 3;
    CoreStmt effect;
    effect.kind = CoreStmtKind::Print;
    effect.org = origin;
    effect.print.push_back(CorePrintArg { .kind = CorePrintArg::Text, .str = "effect" });
    conditional->otherwise->stmts.push_back(std::move(effect));
    conditional->otherwise->value = make_unique<CoreExpr>();
    conditional->otherwise->value->kind = CoreExprKind::Arr;
    conditional->otherwise->value->type = fixed;
    conditional->otherwise->value->org = origin;
    conditional->otherwise->value->elems.push_back(Integer(u8, "65"));
    auto block = make_unique<CoreExpr>();
    block->kind = CoreExprKind::Block;
    block->type = fixed;
    block->org = origin;
    block->then = make_unique<CoreBlock>();
    block->then->scope = 1;
    block->then->value = std::move(conditional);
    core.impls[0].body.stmts[0].expr = std::move(block);
    return core;
}

CoreModule NestedDeliveryQuery() {
    auto core = FixedCallIntoLimited(2);
    core.files = { "nested-delivery-query.goose" };
    auto u8 = core.IntType(CoreIntTy::U8);
    auto i64 = core.IntType(CoreIntTy::I64);
    auto row2 = core.Intern(CoreType { .kind = CoreType::Arr, .elem = u8, .count = 2 });
    auto row3 = core.Intern(CoreType { .kind = CoreType::Arr, .elem = u8, .count = 3 });
    auto rows2 = core.Intern(CoreType { .kind = CoreType::Arr, .elem = row2, .count = 1 });
    auto rows3 = core.Intern(CoreType { .kind = CoreType::Arr, .elem = row3, .count = 1 });
    auto limited = core.Intern(CoreType { .kind = CoreType::Limited, .elem = u8, .count = 2 });
    auto &entry = core.impls[0];
    entry.vars = { CoreVar { "a", rows2, CoreVarKind::Var, 0, origin },
        CoreVar { "b", rows3, CoreVarKind::Var, 0, origin },
        CoreVar { "out", limited, CoreVarKind::Var, 0, origin } };
    entry.body.stmts.clear();
    for (int width : { 2, 3 }) {
        auto row = make_unique<CoreExpr>();
        row->kind = CoreExprKind::Arr;
        row->type = width == 2 ? row2 : row3;
        row->org = origin;
        row->elems.push_back(Integer(u8, "65"));
        row->elems.push_back(Integer(u8, "66"));
        if (width == 3) row->elems.push_back(Integer(u8, "67"));
        auto rows = make_unique<CoreExpr>();
        rows->kind = CoreExprKind::Arr;
        rows->type = width == 2 ? rows2 : rows3;
        rows->org = origin;
        rows->elems.push_back(std::move(row));
        CoreStmt initialized;
        initialized.kind = CoreStmtKind::Let;
        initialized.var = width - 2;
        initialized.expr = std::move(rows);
        initialized.org = origin;
        entry.body.stmts.push_back(std::move(initialized));
    }
    auto sliced = [&](int local, CoreTypeId row) {
        auto value = make_unique<CoreExpr>();
        value->kind = CoreExprKind::Slice;
        value->type = core.Intern(CoreType { .kind = CoreType::Slice, .mut = CoreMut::Const, .elem = row });
        value->mut = CoreMut::Const;
        value->org = origin;
        value->view = make_unique<CoreView>();
        value->view->place = make_unique<CorePlace>();
        value->view->place->index = local;
        return value;
    };
    auto choose = make_unique<CoreExpr>();
    choose->kind = CoreExprKind::If;
    choose->type = core.Intern(CoreType { .kind = CoreType::Slice, .mut = CoreMut::Const, .elem = row3 });
    choose->org = origin;
    choose->a = make_unique<CoreExpr>();
    choose->a->kind = CoreExprKind::Bool;
    choose->a->type = core.Intern(CoreType { .kind = CoreType::Bool });
    choose->a->flag = false;
    choose->then = make_unique<CoreBlock>();
    choose->then->scope = 1;
    CoreStmt dead;
    dead.kind = CoreStmtKind::Abort;
    dead.message = "dead";
    dead.org = origin;
    choose->then->stmts.push_back(std::move(dead));
    choose->then->value = sliced(0, row2);
    choose->otherwise = make_unique<CoreBlock>();
    choose->otherwise->scope = 2;
    CoreStmt effect;
    effect.kind = CoreStmtKind::Print;
    effect.org = origin;
    effect.print.push_back(CorePrintArg { .kind = CorePrintArg::Text, .str = "effect" });
    choose->otherwise->stmts.push_back(std::move(effect));
    choose->otherwise->value = sliced(1, row3);
    auto read = make_unique<CoreExpr>();
    read->kind = CoreExprKind::Read;
    read->type = row3;
    read->org = origin;
    read->place = make_unique<CorePlace>();
    read->place->kind = CorePlace::Elem;
    read->place->org = origin;
    read->place->expr = Integer(i64, "0");
    read->place->view = make_unique<CoreView>();
    read->place->view->kind = CoreView::Val;
    read->place->view->expr = std::move(choose);
    CoreStmt initialized;
    initialized.kind = CoreStmtKind::Let;
    initialized.var = 2;
    initialized.expr = std::move(read);
    initialized.org = origin;
    entry.body.stmts.push_back(std::move(initialized));
    return core;
}

CoreModule Fixture(string_view name) {
    if (name == "low-fuel-block-value") return LowFuelBlockValue();
    if (name == "nested-query-overflow") return NestedDeliveryQuery();
    if (name == "escaping-live-varr") return EscapingDeliveryBranch(true);
    if (name == "escaping-live-fixed") return EscapingDeliveryBranch(false);
    if (name == "fixed-call-fit") return FixedCallIntoLimited(3);
    if (name == "fixed-call-overflow") return FixedCallIntoLimited(1);
    if (name == "waiting-named-break") return BorrowedWaitingNamed(CoreStmtKind::Break);
    if (name == "waiting-named-continue") return BorrowedWaitingNamed(CoreStmtKind::Continue);
    if (name == "waiting-child-break") return BorrowedWaitingChild(CoreStmtKind::Break);
    if (name == "waiting-child-continue") return BorrowedWaitingChild(CoreStmtKind::Continue);
    if (name == "waiting-rearm-break") return BorrowedWaiting(CoreStmtKind::Break);
    if (name == "waiting-rearm-continue") return BorrowedWaiting(CoreStmtKind::Continue);
    if (name == "waiting-after-named") return WaitingAfterNamedValue();
    if (name == "named-layout-helper-read") return NamedHelperRead();
    if (name == "named-layout-nested-read") return NamedNestedRead();
    if (name == "named-layout-result") return NamedLayout(false);
    if (name == "adapted-open") return AdaptedCall(AdaptedCase::Open);
    if (name == "adapted-built") return AdaptedCall(AdaptedCase::Built);
    if (name == "adapted-nested") return AdaptedCall(AdaptedCase::Nested);
    if (name == "waiting-delegated-argument") return WaitingArgument(false);
    if (name == "waiting-guarded-argument") return WaitingArgument(true);
    if (name == "waiting-guarded-call") {
        auto core = DeferredTargetCleanup();
        auto bytes = core.impls[1].results[0].type;
        auto &initial = core.impls[2].body.stmts[0];
        initial.expr = make_unique<CoreExpr>();
        initial.expr->kind = CoreExprKind::Call;
        initial.expr->type = bytes;
        initial.expr->ctx = 3;
        initial.expr->org = origin;
        auto &helper = core.impls[3];
        helper.results = { {bytes, CoreRequest::Value} };
        helper.summary.constructs = {0};
        auto escaped = std::move(helper.body.stmts[0]);
        helper.body.stmts.clear();
        helper.body.value = make_unique<CoreExpr>();
        helper.body.value->kind = CoreExprKind::Block;
        helper.body.value->type = bytes;
        helper.body.value->org = origin;
        helper.body.value->then = make_unique<CoreBlock>();
        helper.body.value->then->scope = 1;
        helper.body.value->then->stmts.push_back(std::move(escaped));
        helper.body.value->then->value = Bytes(bytes, 67);
        return core;
    }
    if (name == "waiting-own-catch") {
        auto core = WaitingCompletion(false);
        auto bytes = core.impls[1].results[0].type;
        core.targets[0].members = {1};
        core.impls[1].summary.needs.clear();
        core.impls[1].summary.escapes.clear();
        auto &laterEscape = core.impls[1].body.value->values[1]->then->stmts[0];
        laterEscape.values.push_back(Bytes(bytes, 70));
        laterEscape.values.push_back(Bytes(bytes, 68));
        CoreStmt called;
        called.kind = CoreStmtKind::Expr;
        called.org = origin;
        called.expr = make_unique<CoreExpr>();
        called.expr->kind = CoreExprKind::Call;
        called.expr->ctx = 2;
        called.expr->org = origin;
        core.impls[1].body.value->values[0]->then->stmts.push_back(std::move(called));
        CoreImpl helper;
        helper.name = "return_to_producer";
        helper.body.scope = 0;
        helper.summary.needs = {0};
        helper.summary.escapes = {0};
        helper.summary.aborts = true;
        CoreStmt escaped;
        escaped.kind = CoreStmtKind::ReturnFrom;
        escaped.target = 0;
        escaped.org = origin;
        escaped.values.push_back(Bytes(bytes, 70));
        escaped.values.push_back(Bytes(bytes, 68));
        helper.body.stmts.push_back(std::move(escaped));
        core.impls.push_back(std::move(helper));
        core.contexts.push_back(CoreContext { .impl = 2 });
        return core;
    }
    if (name == "waiting-nested-return") {
        auto core = WaitingCompletion(false);
        auto bytes = core.impls[1].results[0].type;
        CoreStmt returned;
        returned.kind = CoreStmtKind::RetValues;
        returned.org = origin;
        returned.values.push_back(Bytes(bytes, 70));
        returned.values.push_back(Bytes(bytes, 68));
        core.impls[1].body.value->values[0]->then->stmts.push_back(std::move(returned));
        return core;
    }
    if (name == "waiting-stop") {
        auto core = WaitingCompletion(false);
        CoreStmt stopped;
        stopped.kind = CoreStmtKind::Exit;
        stopped.org = origin;
        stopped.expr = Integer(core.IntType(CoreIntTy::I64), "7");
        core.impls[1].body.value->values[0]->then->stmts.push_back(std::move(stopped));
        return core;
    }
    if (name == "waiting-built-before-tail") {
        auto core = WaitingCompletion(false);
        auto &producer = core.impls[1];
        auto bytes = producer.results[0].type;
        producer.results[1].namedLocal = 0;
        producer.vars = { {"named", bytes, CoreVarKind::Var, 0, origin} };
        producer.body.stmts.clear();
        CoreStmt initialized;
        initialized.kind = CoreStmtKind::Let;
        initialized.var = 0;
        initialized.org = origin;
        initialized.expr = Bytes(bytes, 65);
        producer.body.stmts.push_back(std::move(initialized));
        auto &first = producer.body.value->values[0];
        first->then->scope = 1;
        first->then->value->elems[1]->then->scope = 2;
        first->then->value->elems[1]->otherwise->scope = 3;
        first->then->stmts.clear();
        CoreStmt escaped;
        escaped.kind = CoreStmtKind::ReturnFrom;
        escaped.target = 0;
        escaped.org = origin;
        first->then->stmts.push_back(std::move(escaped));
        auto named = make_unique<CoreExpr>();
        named->kind = CoreExprKind::ResultLocal;
        named->type = bytes;
        named->var = 0;
        named->org = origin;
        producer.body.value->values[1] = std::move(named);
        return core;
    }
    if (name == "waiting-implicit") return WaitingCompletion(false);
    if (name == "waiting-explicit") return WaitingCompletion(true);
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

void MutableParameterRebindingKeepsBodyRootInference() {
    for (auto mutability : { CoreMut::Const, CoreMut::Mut }) {
        CoreModule core;
        core.profile = CoreProfile::Construction;
        core.files = { "parameter-rebind.goose" };
        auto integer = core.IntType(CoreIntTy::I64);
        auto slice = core.Intern(CoreType { .kind = CoreType::Slice, .mut = mutability, .elem = integer });
        CoreImpl entry;
        entry.name = "entry";
        entry.body.scope = 0;
        core.impls.push_back(std::move(entry));
        CoreImpl rebind;
        rebind.name = "rebind";
        rebind.body.scope = 0;
        rebind.vars = { { "view", slice, CoreVarKind::Var, 0, origin },
                       { "source", slice, CoreVarKind::Let, 0, origin } };
        rebind.params = { { 0, false }, { 1, false } };
        rebind.summary.unknown = true;
        CoreStmt statement;
        statement.kind = CoreStmtKind::Rebind;
        statement.var = 0;
        statement.org = origin;
        statement.expr = make_unique<CoreExpr>();
        statement.expr->kind = CoreExprKind::Read;
        statement.expr->type = slice;
        statement.expr->place = make_unique<CorePlace>();
        statement.expr->place->index = 1;
        rebind.body.stmts.push_back(std::move(statement));
        core.impls.push_back(std::move(rebind));
        CoreContext entryContext;
        entryContext.impl = 0;
        core.contexts.push_back(std::move(entryContext));
        CoreContext rebindContext;
        rebindContext.impl = 1;
        rebindContext.varroots = { { 0, { { CoreRootRef::Param, 0 } } },
                                  { 1, { { CoreRootRef::Param, 1 } } } };
        core.contexts.push_back(std::move(rebindContext));
        auto high = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
        Valid(high);
        Valid(GirToLow(high).Lower());
        auto forged = high;
        auto &slots = *forged.funcs[1].roots.slots;
        auto bound = find_if(slots.begin(), slots.end(), [](auto &row) { return row.first == 0; });
        if (bound == slots.end()) slots.push_back({ 0, { { CoreRootRef::Param, 0 } } });
        else bound->second = { { CoreRootRef::Param, 0 } };
        auto violation = GirVerifier(forged).Verify();
        assert(violation && violation->code == "GIR-V050");
        assert(violation->message.find("root info omits a root stored by the body") != string::npos);
    }
}

void RawCompletionAliasesPreserveTheWritingPhase() {
    auto core = Fixture("adapted-open");
    auto high = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
    Valid(high);
    auto original = GirToLow(high).Lower();
    Valid(original);
    enum class Alias { Direct, Local, Branch };
    for (auto transport : { Alias::Direct, Alias::Local, Alias::Branch }) for (bool repeated : { false, true }) {
        auto candidate = original;
        bool changed = false;
        for (auto &function : candidate.funcs) {
            int next = 0;
            for (auto &block : function.blocks) {
                for (auto [value, type] : block.params) next = max(next, value + 1);
                for (auto &instruction : block.insts) if (GirDefinesValue(instruction)) next = max(next, instruction.res + 1);
            }
            for (size_t block = 0; block < function.blocks.size(); block++) {
                auto &instructions = function.blocks[block].insts;
                auto finish = find_if(instructions.begin(), instructions.end(), [](const auto &instruction) {
                    return instruction.op == GirOp::ControlAttemptFinish;
                });
                if (finish == instructions.end()) continue;
                auto completed = *finish;
                auto position = finish - instructions.begin();
                if (transport == Alias::Direct) {
                    if (repeated) instructions.insert(finish + 1, completed);
                } else if (transport == Alias::Local) {
                    auto member = (int)function.members.size();
                    function.members.push_back(GirMember { .kind = GirMember::Scalar, .ty = candidate.PtrType(), .scope = 0 });
                    GirInst saved; saved.op = GirOp::LocalSet; saved.idx = member; saved.a = completed.a;
                    GirInst restored; restored.op = GirOp::LocalGet; restored.res = next; restored.idx = member;
                    auto aliasFinish = completed; aliasFinish.a = next;
                    if (repeated) {
                        instructions.insert(instructions.begin() + position, saved);
                        instructions.insert(instructions.begin() + position + 2, { restored, aliasFinish });
                    } else {
                        instructions[position] = aliasFinish;
                        instructions.insert(instructions.begin() + position, { saved, restored });
                    }
                } else {
                    GirBlock continuation { { { next, candidate.PtrType() } }, vector<GirInst>(finish, instructions.end()) };
                    instructions.erase(finish, instructions.end());
                    GirInst nextBlock; nextBlock.op = GirOp::Br; nextBlock.idx = (int)function.blocks.size(); nextBlock.vals = { completed.a };
                    instructions.push_back(std::move(nextBlock));
                    if (repeated) {
                        auto aliasFinish = completed; aliasFinish.a = next;
                        continuation.insts.insert(continuation.insts.begin() + 1, aliasFinish);
                    } else continuation.insts.front().a = next;
                    function.blocks.push_back(std::move(continuation));
                }
                changed = true;
                break;
            }
            if (changed) break;
        }
        auto violation = GirVerifier(candidate).Verify();
        if (repeated)
            assert(changed && violation && violation->code == "GIR-V090" &&
                violation->message.find("finish does not own an active writer") != string::npos);
        else assert(changed && !violation);
    }
}

void FixedCallEffectsPrecedeTheKnownReceivingCheck() {
    for (int64_t capacity : { 1, 3 }) {
        auto core = FixedCallIntoLimited(capacity);
        CoreWriter writer(core); writer.Write();
        auto high = GirLowerer(core, writer.FileTable(), writer.OriginTable(),
            [&](const CoreOrigin &source) { return writer.OriginId(source); }).Lower();
        assert(!GirVerifier(high).Verify());
        auto &instructions = high.funcs[0].blocks[0].insts;
        int call = -1, open = -1;
        map<int, string> integers;
        for (size_t position = 0; position < instructions.size(); position++) {
            auto &instruction = instructions[position];
            if (instruction.op == GirOp::Int) integers[instruction.res] = instruction.text;
            if (instruction.op == GirOp::Call) call = (int)position;
            if (instruction.op == GirOp::DestOpen) {
                open = (int)position;
                assert(instruction.knownCount && integers.at(*instruction.knownCount) == "2");
            }
            assert(instruction.op != GirOp::DestStage && instruction.op != GirOp::DestFit);
        }
        assert(call >= 0 && open > call);
        auto unsafe = high;
        bool changed = false;
        for (auto &instruction : unsafe.funcs[0].blocks[0].insts)
            if (instruction.op == GirOp::Int && integers.count(instruction.res) && instruction.text == "2") {
                instruction.text = "1"; changed = true;
            }
        auto rejected = GirVerifier(unsafe).Verify();
        assert(changed && rejected && rejected->code == "GIR-V060");
    }
}

void ReturningFixedBranchPrecedesTheReceivingCheck() {
    auto core = EscapingDeliveryBranch(false);
    CoreWriter writer(core); writer.Write();
    auto high = GirLowerer(core, writer.FileTable(), writer.OriginTable(),
        [&](const CoreOrigin &source) { return writer.OriginId(source); }).Lower();
    assert(!GirVerifier(high).Verify());
    int snapshots = 0, opens = 0;
    for (auto &block : high.funcs[0].blocks) {
        bool opened = false;
        for (auto &instruction : block.insts) {
            assert(instruction.op != GirOp::DestStage && instruction.op != GirOp::DestFit);
            if (instruction.op == GirOp::DestOpen) { assert(instruction.knownCount); opened = true; opens++; }
            if (instruction.op == GirOp::DestSnapshot) { assert(opened); snapshots++; }
        }
    }
    assert(opens == 1 && snapshots == 1);
}


int NextValue(const GirFunc &function) {
    int next = 0;
    for (auto &block : function.blocks) {
        for (auto [value, type] : block.params) next = max(next, value + 1);
        for (auto &inst : block.insts) if (GirDefinesValue(inst)) next = max(next, inst.res + 1);
    }
    return next;
}

GirModule LimitedLow(bool staged) {
    auto core = staged ? EscapingDeliveryBranch(true) : FixedCallIntoLimited(3);
    auto high = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
    Valid(high);
    auto low = GirToLow(high).Lower();
    Valid(low);
    return low;
}

void LimitedCursorControls() {
    for (int control = 0; control < 33; control++) {
        auto low = LimitedLow((control >= 4 && control <= 12) || (control >= 18 && control <= 22));
        auto &function = low.funcs[0];
        int cursor = -1, firstRaw = -1;
        for (auto &block : function.blocks) for (auto &inst : block.insts)
            if (inst.op == GirOp::ControlReceivingNew && cursor < 0) cursor = inst.a;
        for (auto &block : function.blocks) for (auto &inst : block.insts)
            if (inst.op == GirOp::ControlReceivingCurrent && firstRaw < 0) firstRaw = inst.res;
        assert(cursor >= 0 && firstRaw >= 0);
        bool changed = false;
        for (auto &block : function.blocks) {
            for (size_t position = 0; position < block.insts.size() && !changed; position++) {
                auto &inst = block.insts[position];
                if (control == 0 && inst.op == GirOp::PStore && inst.a == cursor) {
                    block.insts.erase(block.insts.begin() + position); changed = true;
                } else if (control == 1 && inst.op == GirOp::StackBump) {
                    auto amount = inst.b;
                    for (auto &sourceBlock : function.blocks) for (auto &source : sourceBlock.insts)
                        if (source.res == amount && source.op == GirOp::Int) { source.text = "4"; changed = true; }
                } else if (control == 2 && inst.op == GirOp::ControlReceivingNew) {
                    inst.b = cursor; changed = true;
                } else if (control == 3 && inst.op == GirOp::StackBump) {
                    auto next = NextValue(function);
                    GirInst amount; amount.op = GirOp::Int; amount.res = next++; amount.ty = low.IntType(CoreIntTy::I64); amount.text = "4";
                    int active = firstRaw;
                    for (auto &sourceBlock : function.blocks) for (auto &source : sourceBlock.insts)
                        if (source.res == inst.a && source.op == GirOp::ControlAttemptStack) active = source.a;
                    GirInst start; start.op = GirOp::ControlAttemptStart; start.res = next++; start.a = active;
                    GirInst outside; outside.op = GirOp::PtrOffset; outside.res = next++; outside.a = start.res; outside.b = amount.res; outside.idx = 1;
                    GirInst release; release.op = GirOp::StackRelease; release.a = cursor; release.b = outside.res;
                    block.insts.insert(block.insts.begin() + position, { amount, start, outside, release }); changed = true;
                } else if ((control >= 13 && control <= 17) && inst.op == GirOp::StackBump) {
                    auto next = NextValue(function);
                    int active = firstRaw;
                    for (auto &sourceBlock : function.blocks) for (auto &source : sourceBlock.insts)
                        if (source.res == inst.a && source.op == GirOp::ControlAttemptStack) active = source.a;
                    GirInst start; start.op = GirOp::ControlAttemptStart; start.res = next++; start.a = active;
                    GirInst distance; distance.op = GirOp::Int; distance.res = next++; distance.ty = low.IntType(CoreIntTy::I64); distance.text = control == 16 ? "9223372036854775807" : "4";
                    GirInst outside; outside.op = GirOp::PtrOffset; outside.res = next++; outside.a = start.res;
                    outside.b = control == 15 ? function.blocks[0].params[0].first : distance.res; outside.idx = 1;
                    GirInst byte; byte.op = GirOp::Int; byte.res = next++; byte.ty = low.IntType(CoreIntTy::U8); byte.text = "0";
                    GirInst write; write.op = GirOp::PStore; write.ty = low.IntType(CoreIntTy::U8); write.b = byte.res;
                    if (control == 17) {
                        auto safeBlock = (int)function.blocks.size();
                        auto badBlock = safeBlock + 1;
                        GirBlock continuation { {}, vector<GirInst>(block.insts.begin() + position, block.insts.end()) };
                        GirBlock overflow;
                        GirInst tooMuch; tooMuch.op = GirOp::Int; tooMuch.res = next++; tooMuch.ty = low.IntType(CoreIntTy::I64); tooMuch.text = "4";
                        GirInst bump = inst; bump.b = tooMuch.res;
                        GirInst resume; resume.op = GirOp::Br; resume.idx = safeBlock;
                        overflow.insts = { tooMuch, bump, resume };
                        GirInst large; large.op = GirOp::Int; large.res = next++; large.ty = low.IntType(CoreIntTy::I64); large.text = "256";
                        GirInst narrow; narrow.op = GirOp::Conv; narrow.res = next++; narrow.a = large.res;
                        narrow.ty = low.IntType(CoreIntTy::I64); narrow.ty2 = low.IntType(CoreIntTy::U8); narrow.conv = CoreConvKind::AsUnchecked;
                        GirInst zero; zero.op = GirOp::Int; zero.res = next++; zero.ty = low.IntType(CoreIntTy::U8); zero.text = "0";
                        GirInst compare; compare.op = GirOp::Cmp; compare.res = next++; compare.ty = low.IntType(CoreIntTy::U8);
                        compare.cmp = CoreCmpOp::Eq; compare.a = narrow.res; compare.b = zero.res;
                        GirInst branch; branch.op = GirOp::CondBr; branch.a = compare.res; branch.idx = badBlock; branch.idx2 = safeBlock;
                        block.insts.erase(block.insts.begin() + position, block.insts.end());
                        block.insts.insert(block.insts.end(), { large, narrow, zero, compare, branch });
                        function.blocks.push_back(std::move(continuation)); function.blocks.push_back(std::move(overflow));
                    } else if (control == 14) {
                        GirBlock continuation { { { next++, low.PtrType() } }, vector<GirInst>(block.insts.begin() + position, block.insts.end()) };
                        write.a = continuation.params[0].first;
                        continuation.insts.insert(continuation.insts.begin(), { byte, write });
                        block.insts.erase(block.insts.begin() + position, block.insts.end());
                        block.insts.insert(block.insts.end(), { start, distance, outside });
                        GirInst branch; branch.op = GirOp::Br; branch.idx = (int)function.blocks.size(); branch.vals = { outside.res };
                        block.insts.push_back(branch); function.blocks.push_back(std::move(continuation));
                    } else {
                        GirMember member; member.kind = GirMember::Scalar; member.ty = low.PtrType(); member.scope = 0;
                        auto local = (int)function.members.size(); function.members.push_back(member);
                        GirInst saved; saved.op = GirOp::LocalSet; saved.a = outside.res; saved.idx = local;
                        GirInst restored; restored.op = GirOp::LocalGet; restored.res = next++; restored.ty = low.PtrType(); restored.idx = local;
                        write.a = restored.res;
                        block.insts.insert(block.insts.begin() + position, { start, distance, outside, saved, restored, byte, write });
                    }
                    changed = true;
                } else if (control >= 25 && control <= 28 && inst.op == (control == 26 ? GirOp::PStore : GirOp::StackBump) && (control != 26 || inst.a == cursor)) {
                    auto next = NextValue(function);
                    GirInst offset; offset.op = GirOp::Int; offset.res = next++; offset.ty = low.IntType(CoreIntTy::I64); offset.text = "0";
                    GirInst address; address.op = GirOp::PtrOffset; address.res = next++; address.a = cursor; address.b = offset.res; address.idx = 1;
                    int data = -1;
                    for (auto &candidateBlock : function.blocks) for (auto &candidate : candidateBlock.insts)
                        if (candidate.op == GirOp::PStore && candidate.a == cursor) data = candidate.b;
                    assert(data >= 0);
                    if (control == 26) {
                        inst.a = address.res;
                        block.insts.insert(block.insts.begin() + position, { offset, address });
                    } else if (control == 27) {
                        GirInst byte; byte.op = GirOp::StaticBytes; byte.res = next++; byte.bytes = { 0 };
                        GirInst amount; amount.op = GirOp::Int; amount.res = next++; amount.ty = low.IntType(CoreIntTy::I64); amount.text = "1";
                        GirInst overwrite; overwrite.op = GirOp::BytesCopy; overwrite.a = cursor; overwrite.b = byte.res; overwrite.vals = { amount.res };
                        block.insts.insert(block.insts.begin() + position, { byte, amount, overwrite });
                    } else if (control == 28) {
                        GirInst load; load.op = GirOp::PLoad; load.res = next++; load.ty = low.PtrType(); load.a = cursor;
                        GirInst distance; distance.op = GirOp::Int; distance.res = next++; distance.ty = low.IntType(CoreIntTy::I64); distance.text = "4";
                        GirInst outside = address; outside.res = next++; outside.a = load.res; outside.b = distance.res;
                        GirInst byte; byte.op = GirOp::Int; byte.res = next++; byte.ty = low.IntType(CoreIntTy::U8); byte.text = "0";
                        GirInst write; write.op = GirOp::PStore; write.ty = byte.ty; write.a = outside.res; write.b = byte.res;
                        block.insts.insert(block.insts.begin() + position, { load, distance, outside, byte, write });
                    } else {
                        GirInst overwrite; overwrite.op = GirOp::PStore; overwrite.ty = low.PtrType(); overwrite.a = address.res; overwrite.b = data;
                        block.insts.insert(block.insts.begin() + position, { offset, address, overwrite });
                    }
                    changed = true;
                } else if (control >= 29 && inst.op == GirOp::StackBump) {
                    auto next = NextValue(function);
                    if (control == 30) {
                        auto oldStack = inst.a;
                        GirBlock continuation { { { next++, low.PtrType() } }, vector<GirInst>(block.insts.begin() + position, block.insts.end()) };
                        continuation.insts.front().a = continuation.params[0].first;
                        block.insts.erase(block.insts.begin() + position, block.insts.end());
                        GirInst branch; branch.op = GirOp::Br; branch.idx = (int)function.blocks.size(); branch.vals = { oldStack };
                        block.insts.push_back(branch); function.blocks.push_back(std::move(continuation));
                    } else {
                        GirMember member; member.kind = GirMember::Scalar; member.ty = low.PtrType(); member.scope = 0;
                        auto local = (int)function.members.size(); function.members.push_back(member);
                        if (control == 29) {
                            GirInst saved; saved.op = GirOp::LocalSet; saved.a = inst.a; saved.idx = local;
                            GirInst restored; restored.op = GirOp::LocalGet; restored.res = next++; restored.ty = low.PtrType(); restored.idx = local;
                            inst.a = restored.res;
                            block.insts.insert(block.insts.begin() + position, { saved, restored });
                        } else {
                            GirInst cell; cell.op = GirOp::FrameAddr; cell.res = next++; cell.idx = local;
                            GirInst spill; spill.op = GirOp::PStore; spill.ty = low.PtrType(); spill.a = cell.res; spill.b = cursor;
                            if (control == 31) block.insts.insert(block.insts.begin() + position, { cell, spill });
                            else {
                                GirMember bytes; bytes.kind = GirMember::Bytes; bytes.size = 4; bytes.scope = 0;
                                auto storage = (int)function.members.size(); function.members.push_back(bytes);
                                GirInst base = cell; base.res = next++; base.idx = storage;
                                GirInst one; one.op = GirOp::Int; one.res = next++; one.ty = low.IntType(CoreIntTy::I64); one.text = "1";
                                GirInst data; data.op = GirOp::PtrOffset; data.res = next++; data.a = base.res; data.b = one.res; data.idx = 1;
                                spill.b = data.res;
                                GirInst read; read.op = GirOp::PLoad; read.res = next++; read.ty = low.PtrType(); read.a = cell.res;
                                block.insts.insert(block.insts.begin() + position, { cell, base, one, data, spill, read });
                            }
                        }
                    }
                    changed = true;
                } else if ((control == 23 || control == 24) && inst.op == GirOp::StackBump) {
                    auto next = NextValue(function);
                    auto active = firstRaw;
                    for (auto &candidateBlock : function.blocks) for (auto &candidate : candidateBlock.insts)
                        if (candidate.res == inst.a && candidate.op == GirOp::ControlAttemptStack) active = candidate.a;
                    GirInst start; start.op = GirOp::ControlAttemptStart; start.res = next++; start.a = active;
                    GirInst source; source.op = GirOp::StaticBytes; source.res = next++; source.bytes = { 0,0 };
                    GirInst count; count.op = GirOp::Int; count.res = next++; count.ty = low.IntType(CoreIntTy::I64); count.text = control == 23 ? "2" : "1";
                    GirInst fill; fill.op = GirOp::BytesFill; fill.a = start.res; fill.b = source.res; fill.vals = { count.res }; fill.idx = 2;
                    block.insts.insert(block.insts.begin() + position, { start, source, count, fill }); changed = true;
                } else if (control == 4 && inst.op == GirOp::ControlAttemptStage) {
                    inst.vals[0] = inst.a; changed = true;
                } else if (control == 5 && inst.op == GirOp::ControlAttemptStage) {
                    auto old = inst.a;
                    GirInst stale; stale.op = GirOp::ControlAttemptPrefix; stale.a = old; stale.res = NextValue(function);
                    block.insts.insert(block.insts.begin() + position + 1, stale); changed = true;
                } else if (control == 6 && inst.op == GirOp::ControlAttemptFit) {
                    inst.b = inst.a; changed = true;
                } else if (control == 7 && inst.op == GirOp::ControlAttemptStage) {
                    auto next = NextValue(function);
                    GirInst receiving; receiving.op = GirOp::ControlAttemptReceiving; receiving.res = next++; receiving.a = inst.a;
                    GirInst reserved; reserved.op = GirOp::ControlExitReserve; reserved.res = next++; reserved.a = receiving.res;
                    block.insts.insert(block.insts.begin() + position, { receiving, reserved }); changed = true;
                } else if (control == 8 && inst.op == GirOp::ControlAttemptFit) {
                    auto next = NextValue(function);
                    GirInst repeated = inst; repeated.res = next++; repeated.a = inst.res;
                    block.insts.insert(block.insts.begin() + position + 1, repeated); changed = true;
                } else if (control == 18 && inst.op == GirOp::ControlAttemptFit) {
                    auto next = NextValue(function);
                    GirInst bytes; bytes.op = GirOp::StaticBytes; bytes.res = next++; bytes.bytes = { 4,0,0,0,0,0,0,0 };
                    GirInst amount; amount.op = GirOp::Int; amount.res = next++; amount.ty = low.IntType(CoreIntTy::I64); amount.text = "8";
                    GirInst copy; copy.op = GirOp::BytesCopy; copy.a = inst.a; copy.b = bytes.res; copy.vals = { amount.res };
                    block.insts.insert(block.insts.begin() + position, { bytes, amount, copy }); changed = true;
                } else if (control == 19 && inst.op == GirOp::ControlAttemptFit) {
                    auto next = NextValue(function);
                    GirInst progress; progress.op = GirOp::ControlAttemptProgress; progress.res = next++; progress.a = inst.a;
                    GirInst opened; opened.op = GirOp::Int; opened.res = next++; opened.ty = low.IntType(CoreIntTy::I64);
                    opened.text = to_string((int)GirConstructionProgress::Open);
                    GirInst write; write.op = GirOp::PStore; write.ty = low.IntType(CoreIntTy::I64); write.a = progress.res; write.b = opened.res;
                    block.insts.insert(block.insts.begin() + position, { progress, opened, write }); changed = true;
                } else if (control == 20 && inst.op == GirOp::ControlAttemptFit) {
                    auto old = inst.a, fitted = inst.res;
                    block.insts.erase(block.insts.begin() + position);
                    for (auto &sourceBlock : function.blocks) for (auto &source : sourceBlock.insts) {
                        if (source.a == fitted) source.a = old;
                        if (source.b == fitted) source.b = old;
                        for (auto &value : source.vals) if (value == fitted) value = old;
                        for (auto &value : source.vals2) if (value == fitted) value = old;
                    }
                    changed = true;
                } else if (control == 21 && inst.op == GirOp::ControlAttemptStage) {
                    GirInst pack; pack.op = GirOp::ControlAttemptPack; pack.a = inst.res;
                    block.insts.insert(block.insts.begin() + position + 1, pack); changed = true;
                } else if (control == 22 && inst.op == GirOp::ControlAttemptStage) {
                    auto next = NextValue(function);
                    GirInst zero; zero.op = GirOp::Int; zero.res = next++; zero.ty = low.IntType(CoreIntTy::I64); zero.text = "0";
                    inst.vals[1] = zero.res; inst.vals[2] = zero.res;
                    for (auto &candidateBlock : function.blocks) for (auto &candidate : candidateBlock.insts)
                        if (candidate.op == GirOp::PStore && candidate.a == cursor) inst.vals[0] = candidate.b;
                    for (auto &sourceBlock : function.blocks) for (auto &source : sourceBlock.insts)
                        if (source.op == GirOp::FrameAddr && source.res == cursor) {
                            for (auto &initialBlock : function.blocks) for (auto &initial : initialBlock.insts)
                                if (initial.op == GirOp::PStore && initial.a == cursor)
                                    for (auto &baseBlock : function.blocks) for (auto &base : baseBlock.insts)
                                        if (base.op == GirOp::PtrOffset && base.res == initial.b)
                                            for (auto &ownerBlock : function.blocks) for (auto &owner : ownerBlock.insts)
                                                if (owner.op == GirOp::FrameAddr && owner.res == base.a) function.members[owner.idx].size = 1;
                        }
                    block.insts.insert(block.insts.begin() + position, zero); changed = true;
                } else if (control == 10 && inst.op == GirOp::ControlAttemptFit) {
                    auto next = NextValue(function);
                    GirInst yes; yes.op = GirOp::Bool; yes.res = next++; yes.flag = true;
                    for (auto &predecessor : function.blocks) {
                        auto &branch = predecessor.insts.back();
                        if (branch.op == GirOp::CondBr && branch.idx == (int)(&block - function.blocks.data())) {
                            branch.a = yes.res;
                            predecessor.insts.insert(predecessor.insts.end() - 1, yes); changed = true; break;
                        }
                    }
                } else if (control == 11 && inst.op == GirOp::ControlAttemptFit) {
                    auto next = NextValue(function);
                    GirInst count; count.op = GirOp::Int; count.res = next++; count.ty = low.IntType(CoreIntTy::I64); count.text = "4";
                    GirInst write; write.op = GirOp::PStore; write.ty = low.IntType(CoreIntTy::I64); write.a = inst.a; write.b = count.res;
                    block.insts.insert(block.insts.begin() + position, { count, write }); changed = true;
                } else if (control == 12 && inst.op == GirOp::ControlAttemptFit) {
                    auto next = NextValue(function);
                    auto old = inst.a;
                    GirBlock continuation { { { next, low.PtrType() } }, vector<GirInst>(block.insts.begin() + position, block.insts.end()) };
                    continuation.insts.front().a = next;
                    block.insts.erase(block.insts.begin() + position, block.insts.end());
                    GirInst branch; branch.op = GirOp::Br; branch.idx = (int)function.blocks.size(); branch.vals = { old };
                    block.insts.push_back(branch);
                    function.blocks.push_back(std::move(continuation)); changed = true;
                } else if (control == 9 && inst.op == GirOp::ControlAttemptFit) {
                    auto next = NextValue(function);
                    GirMember member; member.kind = GirMember::Scalar; member.ty = low.PtrType(); member.scope = 0;
                    auto local = (int)function.members.size(); function.members.push_back(member);
                    GirInst saved; saved.op = GirOp::LocalSet; saved.a = inst.a; saved.idx = local;
                    GirInst restored; restored.op = GirOp::LocalGet; restored.res = next++; restored.ty = low.PtrType(); restored.idx = local;
                    inst.a = restored.res;
                    block.insts.insert(block.insts.begin() + position, { saved, restored }); changed = true;
                }
                if (changed) break;
            }
            if (changed) break;
        }
        set<int> defined;
        for (auto &candidate : function.blocks) {
            for (auto [value, type] : candidate.params) defined.insert(value);
            for (auto &source : candidate.insts) if (GirDefinesValue(source)) defined.insert(source.res);
        }
        for (int value = 0, end = NextValue(function); value < end; value++) if (!defined.count(value)) {
            GirInst filler; filler.op = GirOp::Int; filler.res = value; filler.ty = low.IntType(CoreIntTy::I64); filler.text = "0";
            function.blocks[0].insts.insert(function.blocks[0].insts.begin(), filler);
        }
        auto error = GirVerifier(low).Verify();
        if (!changed || ((control == 9 || control == 12 || control == 24 || control == 29 || control == 30 || control == 32) ? error.has_value() : !error || error->code != "GIR-V090")) {
            fprintf(stderr, "control %d: changed=%d error=%s\n", control, changed, error ? error->message.c_str() : "accepted");
            abort();
        }
    }
}

void InlineCursorLocalMembersAreRejected() {
    vector<string> unexpected;
    for (auto access : { GirOp::LocalGet, GirOp::LocalSet }) {
        auto low = LimitedLow(true);
        auto &function = low.funcs[0];
        int cursor = -1, member = -1;
        for (auto &block : function.blocks) for (auto &inst : block.insts)
            if (inst.op == GirOp::ControlReceivingNew) cursor = inst.a;
        for (auto &block : function.blocks) for (auto &inst : block.insts)
            if (inst.op == GirOp::FrameAddr && inst.res == cursor) member = inst.idx;
        assert(cursor >= 0 && member >= 0);
        auto next = NextValue(function);
        bool inserted = false;
        for (auto &block : function.blocks) {
            for (size_t position = 0; position < block.insts.size(); position++) {
                if (block.insts[position].op != GirOp::PStore || block.insts[position].a != cursor) continue;
                GirInst accessInstruction;
                accessInstruction.op = access;
                accessInstruction.idx = member;
                if (access == GirOp::LocalGet) {
                    accessInstruction.res = next;
                    accessInstruction.ty = low.PtrType();
                } else accessInstruction.a = cursor;
                block.insts.insert(block.insts.begin() + position + 1, accessInstruction);
                inserted = true;
                break;
            }
            if (inserted) break;
        }
        assert(inserted);
        auto violation = GirVerifier(low).Verify();
        if (!violation || violation->code != "GIR-V090" ||
            violation->message.find("private inline cursor cell is accessed through a frame local") == string::npos)
            unexpected.push_back(access == GirOp::LocalGet ? "LocalGet" : "LocalSet");
    }
    if (!unexpected.empty()) {
        fprintf(stderr, "inline cursor local access rejection mismatch: ");
        for (size_t index = 0; index < unexpected.size(); index++)
            fprintf(stderr, "%s%s", index ? ", " : "", unexpected[index].c_str());
        fprintf(stderr, "\n");
        abort();
    }
}

void LimitedScratchControls() {
    for (int control = 0; control < 3; control++) {
        auto low = LimitedLow(true);
        auto &function = low.funcs[0];
        auto next = NextValue(function);
        bool changed = false;
        for (auto &block : function.blocks) {
            for (size_t position = 0; position < block.insts.size(); position++) {
                auto original = block.insts[position];
                if (original.op != GirOp::ControlAttemptStage) continue;
                vector<GirInst> extra;
                auto define = [&](GirInst inst) { inst.res = next++; extra.push_back(inst); return inst.res; };
                GirMember owner; owner.kind = GirMember::Bytes; owner.size = 4; owner.scope = 0;
                auto storage = (int)function.members.size(); function.members.push_back(owner);
                GirMember cursor; cursor.kind = GirMember::Scalar; cursor.ty = low.PtrType(); cursor.scope = 0;
                auto cell = (int)function.members.size(); function.members.push_back(cursor);
                GirInst address; address.op = GirOp::FrameAddr; address.idx = storage;
                auto base = define(address);
                GirInst one; one.op = GirOp::Int; one.ty = low.IntType(CoreIntTy::I64); one.text = "1";
                auto offset = define(one);
                GirInst pointer; pointer.op = GirOp::PtrOffset; pointer.a = base; pointer.b = offset; pointer.idx = 1;
                auto data = define(pointer);
                address.idx = cell; auto frame = define(address);
                GirInst initialize; initialize.op = GirOp::PStore; initialize.ty = low.PtrType(); initialize.a = frame; initialize.b = data;
                extra.push_back(initialize);
                GirInst zero = one; zero.text = "0"; auto empty = define(zero);
                GirInst receiving; receiving.op = GirOp::ControlReceivingNew; receiving.a = frame; receiving.b = data; receiving.vals = { empty, empty };
                auto handle = define(receiving);
                GirInst current; current.op = GirOp::ControlReceivingCurrent; current.a = handle;
                auto raw = define(current);
                GirInst capacity = one; capacity.text = "3"; auto count = define(capacity);
                pointer.a = data; pointer.b = count; auto end = define(pointer);
                auto scratch = original.b;
                if (control == 0) {
                    GirInst owned; owned.op = GirOp::StackAt; owned.a = function.blocks[0].params[0].first; owned.idx = function.stacks++;
                    scratch = define(owned);
                }
                if (control == 2) {
                    for (auto &instruction : extra) if (instruction.res == handle) {
                        instruction.a = scratch;
                        GirInst mark; mark.op = GirOp::StackMark; mark.a = scratch;
                        auto result = next++;
                        mark.res = result;
                        instruction.b = result;
                        extra.insert(find_if(extra.begin(), extra.end(), [&](const GirInst &candidate) { return candidate.res == handle; }), mark);
                        break;
                    }
                } else {
                    GirInst stage = original; stage.res = next++; stage.a = raw; stage.b = scratch; stage.vals = { end, count, offset };
                    extra.push_back(stage);
                }
                GirInst cancel; cancel.op = GirOp::ControlReceivingCancel; cancel.a = handle;
                auto certificate = define(cancel);
                GirInst finish; finish.op = GirOp::ControlAttemptCancel; finish.a = certificate; extra.push_back(finish);
                if (control == 2) {
                    block.insts.insert(block.insts.begin() + position, extra.begin(), extra.end() - 2);
                    block.insts.insert(block.insts.begin() + position + extra.size() - 1, extra.end() - 2, extra.end());
                } else block.insts.insert(block.insts.begin() + position + 1, extra.begin(), extra.end());
                changed = true; break;
            }
            if (changed) break;
        }
        auto error = GirVerifier(low).Verify();
        if (!changed || (control == 0 ? error.has_value() : !error || error->code != "GIR-V090" || error->message.find("live private stack") == string::npos)) {
            fprintf(stderr, "scratch control %d: %s\n", control, error ? error->message.c_str() : "accepted");
            abort();
        }
    }
}

void LimitedReceivingAliasControls() {
    for (int control = 0; control < 3; control++) {
        auto low = LimitedLow(true);
        auto &function = low.funcs[0];
        int receiver = -1, alias = -1;
        auto next = NextValue(function);
        for (auto &block : function.blocks) for (size_t position = 0; position < block.insts.size(); position++) {
            auto stage = block.insts[position];
            if (stage.op != GirOp::ControlAttemptStage) continue;
            for (auto &candidateBlock : function.blocks) for (auto &candidate : candidateBlock.insts)
                if (candidate.res == stage.a && candidate.op == GirOp::ControlReceivingCurrent) receiver = candidate.a;
            assert(receiver >= 0);
            GirMember member; member.kind = GirMember::Scalar; member.ty = low.PtrType(); member.scope = 0;
            auto local = (int)function.members.size(); function.members.push_back(member);
            GirInst saved; saved.op = GirOp::LocalSet; saved.a = receiver; saved.idx = local;
            GirInst restored; restored.op = GirOp::LocalGet; restored.res = next++; restored.ty = low.PtrType(); restored.idx = local;
            alias = restored.res;
            block.insts.insert(block.insts.begin() + position, saved);
            block.insts.insert(block.insts.begin() + position + 2, restored);
            goto stored;
        }
        stored:
        assert(alias >= 0);
        bool renewed = false;
        for (auto &block : function.blocks) for (auto &inst : block.insts)
            if (!renewed && inst.op == GirOp::ControlReceivingRenew) { inst.a = alias; renewed = true; }
        assert(renewed);
        if (control == 1) {
            for (auto &block : function.blocks) for (auto &inst : block.insts)
                if (inst.op == GirOp::ControlAttemptFit) {
                    auto fitted = inst.res;
                    GirInst query; query.op = GirOp::ControlAttemptPrefix; query.res = fitted; query.a = inst.a;
                    inst = query;
                    for (auto &candidateBlock : function.blocks) for (auto &candidate : candidateBlock.insts) {
                        if (candidate.a == fitted) candidate.a = query.a;
                        if (candidate.b == fitted) candidate.b = query.a;
                        for (auto &value : candidate.vals) if (value == fitted) value = query.a;
                    }
                    goto removed;
                }
        }
        removed:
        if (control == 2) {
            for (size_t blockIndex = 0; blockIndex < function.blocks.size(); blockIndex++) {
                auto &block = function.blocks[blockIndex];
                for (size_t position = 0; position < block.insts.size(); position++)
                    if (block.insts[position].op == GirOp::ControlReceivingRenew) {
                        GirBlock continuation { { { next++, low.PtrType() } }, vector<GirInst>(block.insts.begin() + position, block.insts.end()) };
                        continuation.insts.front().a = continuation.params[0].first;
                        block.insts.erase(block.insts.begin() + position, block.insts.end());
                        GirInst branch; branch.op = GirOp::Br; branch.idx = (int)function.blocks.size(); branch.vals = { alias };
                        block.insts.push_back(branch); function.blocks.push_back(std::move(continuation));
                        goto aliased;
                    }
            }
        }
        aliased:
        auto error = GirVerifier(low).Verify();
        if (control != 1 ? error.has_value() : !error || error->code != "GIR-V090" || error->message.find("required capacity fit") == string::npos) {
            fprintf(stderr, "receiving alias control %d: %s\n", control, error ? error->message.c_str() : "accepted"); abort();
        }
    }
}


void LimitedFixedCopyUsesTheInlineSpan() {
    auto core = FixedCallIntoLimited(3);
    auto &entry = core.impls[0];
    auto fixed = entry.body.stmts[0].expr->type;
    entry.vars.push_back(CoreVar { "source", fixed, CoreVarKind::Let, 0, origin });
    CoreStmt source; source.kind = CoreStmtKind::Let; source.var = 1; source.org = origin;
    source.expr = std::move(core.impls[1].body.value);
    core.impls[1].body.value = make_unique<CoreExpr>();
    core.impls[1].body.value->kind = CoreExprKind::Arr; core.impls[1].body.value->type = fixed; core.impls[1].body.value->org = origin;
    core.impls[1].body.value->elems.push_back(Integer(core.IntType(CoreIntTy::U8), "65"));
    core.impls[1].body.value->elems.push_back(Integer(core.IntType(CoreIntTy::U8), "66"));
    auto &expression = entry.body.stmts[0].expr;
    expression = make_unique<CoreExpr>(); expression->kind = CoreExprKind::Copy; expression->type = fixed;
    expression->org = origin; expression->place = make_unique<CorePlace>(); expression->place->index = 1;
    entry.body.stmts.insert(entry.body.stmts.begin(), std::move(source));
    core.contexts[0].varroots = { { 1, { { CoreRootRef::Local, 1 } } } };
    auto high = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
    Valid(high);
    Valid(GirToLow(high).Lower());
}


void LimitedStageAfterExposureRemainsExplicitlyUnsupported() {
    auto core = EscapingDeliveryBranch(true);
    auto high = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
    auto &function = high.funcs[0];
    GirInst stage;
    bool found = false;
    for (auto &block : function.blocks) for (size_t position = 0; position < block.insts.size(); position++)
        if (block.insts[position].op == GirOp::DestStage) {
            stage = block.insts[position]; block.insts.erase(block.insts.begin() + position); found = true; goto removed;
        }
    removed:
    assert(found);
    for (auto &block : function.blocks) for (auto &inst : block.insts)
        if (inst.op == GirOp::ReceivingOpen && inst.a == stage.res) inst.a = stage.a;
    for (auto &block : function.blocks) for (size_t position = 0; position < block.insts.size(); position++)
        if (block.insts[position].op == GirOp::DestRenew) {
            auto writer = block.insts[position].res;
            for (auto &candidateBlock : function.blocks) for (auto &candidate : candidateBlock.insts)
                {
                    if (candidate.a == writer) candidate.a = stage.res;
                    if (candidate.b == writer) candidate.b = stage.res;
                    for (auto &value : candidate.vals) if (value == writer) value = stage.res;
                    for (auto &value : candidate.vals2) if (value == writer) value = stage.res;
                }
            stage.a = writer;
            block.insts.insert(block.insts.begin() + position + 1, stage); goto inserted;
        }
    inserted:
    Valid(high);
    try { auto low = GirToLow(high).Lower(); (void)low; assert(false); }
    catch (const GirLowerUnsupported &error) { assert(error.feature == "limited-stage-after-exposure"); }
}


}

int main(int argc, char **argv) try {
    if (argc == 3 && string_view(argv[1]) == "--high") {
        auto core = Fixture(argv[2]);
        auto high = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
        Valid(high);
        printf("%s\n", GirWriter(high).Write().c_str());
        return 0;
    }
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
    for (auto name : { "low-fuel-block-value", "nested-query-overflow", "escaping-live-varr", "escaping-live-fixed", "fixed-call-fit", "fixed-call-overflow", "break", "continue", "call", "named-borrow", "owner-child", "owner-named", "cross-same", "cross-different", "deferred-cleanup", "own-deferred-cleanup", "value-break-cleanup", "nested-break", "nested-continue", "waiting-implicit", "waiting-explicit", "waiting-nested-return", "waiting-stop", "waiting-built-before-tail", "waiting-own-catch", "waiting-guarded-call", "waiting-delegated-argument", "waiting-guarded-argument", "adapted-open", "adapted-built", "adapted-nested", "named-layout-result", "named-layout-nested-read", "named-layout-helper-read", "waiting-rearm-break", "waiting-rearm-continue", "waiting-after-named", "waiting-child-break", "waiting-child-continue", "waiting-named-break", "waiting-named-continue" }) {
        auto core = Fixture(name);
        auto high = GirLowerer(core, core.files, { origin }, [](const CoreOrigin &) { return 0; }).Lower();
        Valid(high);
        Valid(GirToLow(high).Lower());
    }
    MutableParameterRebindingKeepsBodyRootInference();
    FixedCallEffectsPrecedeTheKnownReceivingCheck();
    ReturningFixedBranchPrecedesTheReceivingCheck();
    RawCompletionAliasesPreserveTheWritingPhase();
    LimitedCursorControls();
    InlineCursorLocalMembersAreRejected();
    LimitedScratchControls();
    LimitedReceivingAliasControls();
    LimitedFixedCopyUsesTheInlineSpan();
    LimitedStageAfterExposureRemainsExplicitlyUnsupported();
    printf("compiler_gir_reservations ok\n");
} catch (const CompileError &error) {
    fprintf(stderr, "%s\n", error.msg.c_str());
    return 1;
}
