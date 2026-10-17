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

CoreModule Fixture(string_view name) {
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
    for (auto name : { "break", "continue", "call", "named-borrow", "owner-child", "owner-named", "cross-same", "cross-different", "deferred-cleanup", "own-deferred-cleanup", "value-break-cleanup", "nested-break", "nested-continue", "waiting-implicit", "waiting-explicit", "waiting-nested-return", "waiting-stop", "waiting-built-before-tail", "waiting-own-catch", "waiting-guarded-call", "waiting-delegated-argument", "waiting-guarded-argument", "adapted-open", "adapted-built", "adapted-nested", "named-layout-result", "named-layout-nested-read", "named-layout-helper-read" }) {
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
