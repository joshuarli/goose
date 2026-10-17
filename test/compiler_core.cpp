#ifdef NDEBUG
#undef NDEBUG
#endif
#include "../src/includes.h"
#include "../src/utils.h"
#include "../src/core/core_ir.h"
#include "../src/core/core_json.h"

using namespace goose;

static CoreExprP Int(CoreTypeId type, const char *value) {
    auto expr = make_unique<CoreExpr>();
    expr->kind = CoreExprKind::Lit;
    expr->type = type;
    expr->value = value;
    return expr;
}

static CorePlaceP Local(int index) {
    auto place = make_unique<CorePlace>();
    place->kind = CorePlace::Local;
    place->index = index;
    return place;
}

static CoreExprP Call(CoreTypeId type, CoreTypeId argType) {
    auto expr = make_unique<CoreExpr>();
    expr->kind = CoreExprKind::Call;
    expr->type = type;
    expr->ctx = 0;
    expr->org = CoreOrigin { 0, 1, CoreOriginKind::Call };
    expr->args.emplace_back(CoreArgValue { Int(argType, "1") });
    expr->args.emplace_back(CoreArgConstruct { Int(argType, "2") });
    expr->args.emplace_back(CoreArgReference { CoreMut::Mut, Local(3) });
    return expr;
}

static CorePrintArg Text(const char *text) {
    CorePrintArg arg;
    arg.kind = CorePrintArg::Text;
    arg.str = text;
    return arg;
}

static CorePrintArg ExprArg(CoreExprP expr) {
    CorePrintArg arg;
    arg.kind = CorePrintArg::Expr;
    arg.expr = std::move(expr);
    return arg;
}

static CorePrintArg ViewArg(CoreTypeId type) {
    CorePrintArg arg;
    arg.kind = CorePrintArg::View;
    arg.view = make_unique<CoreView>();
    arg.view->kind = CoreView::Val;
    arg.view->expr = Int(type, "3");
    return arg;
}

static string ConstructionExpressionOrigins(CoreProfile profile) {
    CoreModule module;
    module.files = { "origins.goose" };
    module.profile = profile;
    auto i64 = module.IntType(CoreIntTy::I64);
    auto boolean = module.BoolType();
    CoreType array;
    array.kind = CoreType::Arr;
    array.elem = i64;
    array.count = 1;
    auto arrayType = module.Intern(array);

    CoreImpl impl;
    impl.name = "main";
    impl.body.scope = 0;
    auto append = [&](CoreExprP expr, int line) {
        CoreStmt statement;
        statement.kind = CoreStmtKind::Expr;
        statement.expr = std::move(expr);
        statement.org = CoreOrigin { 0, line, CoreOriginKind::Expr };
        impl.body.stmts.push_back(std::move(statement));
    };

    auto arr = make_unique<CoreExpr>();
    arr->kind = CoreExprKind::Arr;
    arr->type = arrayType;
    arr->elems.push_back(Int(i64, "1"));
    arr->org = CoreOrigin { 0, 2, CoreOriginKind::Expr };
    append(std::move(arr), 2);

    auto fill = make_unique<CoreExpr>();
    fill->kind = CoreExprKind::Fill;
    fill->type = arrayType;
    fill->a = Int(i64, "2");
    fill->org = CoreOrigin { 0, 3, CoreOriginKind::Expr };
    append(std::move(fill), 3);

    auto conditional = make_unique<CoreExpr>();
    conditional->kind = CoreExprKind::If;
    conditional->type = i64;
    conditional->a = make_unique<CoreExpr>();
    conditional->a->kind = CoreExprKind::Bool;
    conditional->a->type = boolean;
    conditional->a->flag = true;
    conditional->then = make_unique<CoreBlock>();
    conditional->then->scope = 1;
    conditional->then->value = Int(i64, "3");
    conditional->otherwise = make_unique<CoreBlock>();
    conditional->otherwise->scope = 2;
    conditional->otherwise->value = Int(i64, "4");
    conditional->org = CoreOrigin { 0, 4, CoreOriginKind::Expr };
    append(std::move(conditional), 4);

    auto block = make_unique<CoreExpr>();
    block->kind = CoreExprKind::Block;
    block->type = i64;
    block->then = make_unique<CoreBlock>();
    block->then->scope = 3;
    block->then->value = Int(i64, "5");
    block->org = CoreOrigin { 0, 5, CoreOriginKind::Expr };
    append(std::move(block), 5);

    module.impls.push_back(std::move(impl));
    return CoreWriter(module).Write();
}

static CoreModule ConstructionShape() {
    CoreModule module;
    module.files = { "construct.goose" };
    module.profile = CoreProfile::Construction;

    auto i64 = module.IntType(CoreIntTy::I64);
    CoreType variableArray;
    variableArray.kind = CoreType::VarArr;
    variableArray.elem = i64;
    auto varr = module.Intern(variableArray);
    CoreType tuple;
    tuple.kind = CoreType::Tuple;
    tuple.parts = { varr, i64, varr };
    auto tupleType = module.Intern(tuple);
    CoreType reference;
    reference.kind = CoreType::Ref;
    reference.elem = i64;
    auto refType = module.Intern(reference);
    CoreType nominal;
    nominal.kind = CoreType::Struct;
    nominal.structid = 0;
    module.Intern(nominal);
    module.structs.push_back(CoreStruct {
        8, { CoreField { i64, CoreVarKind::Var, CoreMut::Mut, 0 } }, "Pair<i64>" });

    CoreImpl impl;
    impl.name = "main";
    impl.params = { CoreParam { 0, false }, CoreParam { 1, false }, CoreParam { 2, true } };
    impl.results = { CoreResultDescriptor { varr, CoreRequest::Value, CoreVarId { 3 } },
                     CoreResultDescriptor { i64, CoreRequest::Register, {} },
                     CoreResultDescriptor { varr, CoreRequest::ElementRun, {} } };
    impl.vars = { CoreVar { "first", i64, CoreVarKind::Let, 0,
                            CoreOrigin { 0, 1, CoreOriginKind::Param } },
                  CoreVar { "second", i64, CoreVarKind::Let, 0,
                            CoreOrigin { 0, 1, CoreOriginKind::Param } },
                  CoreVar { "third", varr, CoreVarKind::Let, 0,
                            CoreOrigin { 0, 1, CoreOriginKind::Param } },
                  CoreVar { "owner", varr, CoreVarKind::Var, 0,
                            CoreOrigin { 0, 1, CoreOriginKind::Let } },
                  CoreVar { "value", i64, CoreVarKind::Let, 0,
                            CoreOrigin { 0, 1, CoreOriginKind::Let } },
                  CoreVar { "alias", refType, CoreVarKind::Let, 0,
                            CoreOrigin { 0, 1, CoreOriginKind::Let } } };
    impl.body.scope = 0;

    auto string = make_unique<CoreExpr>();
    string->kind = CoreExprKind::String;
    string->type = varr;
    string->print.push_back(Text("x"));
    string->print.push_back(ExprArg(Int(i64, "4")));
    string->print.push_back(ViewArg(i64));
    string->org = CoreOrigin { 0, 2, CoreOriginKind::Expr };
    CoreStmt stringStmt;
    stringStmt.kind = CoreStmtKind::Expr;
    stringStmt.expr = std::move(string);
    stringStmt.org = CoreOrigin { 0, 2, CoreOriginKind::Expr };
    impl.body.stmts.push_back(std::move(stringStmt));

    auto copy = make_unique<CoreExpr>();
    copy->kind = CoreExprKind::Copy;
    copy->type = varr;
    copy->place = Local(3);
    copy->org = CoreOrigin { 0, 3, CoreOriginKind::Expr };
    CoreStmt copyStmt;
    copyStmt.kind = CoreStmtKind::Expr;
    copyStmt.expr = std::move(copy);
    copyStmt.org = CoreOrigin { 0, 3, CoreOriginKind::Expr };
    impl.body.stmts.push_back(std::move(copyStmt));

    auto resultLocal = make_unique<CoreExpr>();
    resultLocal->kind = CoreExprKind::ResultLocal;
    resultLocal->var = 3;
    resultLocal->org = CoreOrigin { 0, 4, CoreOriginKind::Expr };
    CoreStmt resultLocalStmt;
    resultLocalStmt.kind = CoreStmtKind::Expr;
    resultLocalStmt.expr = std::move(resultLocal);
    resultLocalStmt.org = CoreOrigin { 0, 4, CoreOriginKind::Expr };
    impl.body.stmts.push_back(std::move(resultLocalStmt));

    auto values = make_unique<CoreExpr>();
    values->kind = CoreExprKind::Values;
    values->values.push_back(Int(i64, "5"));
    values->values.push_back(Int(i64, "6"));
    CoreStmt valuesStmt;
    valuesStmt.kind = CoreStmtKind::Expr;
    valuesStmt.expr = std::move(values);
    valuesStmt.org = CoreOrigin { 0, 5, CoreOriginKind::Expr };
    impl.body.stmts.push_back(std::move(valuesStmt));

    auto receiveCall = Call(tupleType, i64);
    CoreStmt receive;
    receive.kind = CoreStmtKind::Receive;
    receive.vars = { 4, 3 };
    receive.expr = std::move(receiveCall);
    receive.org = CoreOrigin { 0, 6, CoreOriginKind::Call };
    impl.body.stmts.push_back(std::move(receive));

    for (auto kind : { CoreStmtKind::AppendValue, CoreStmtKind::AppendConstruct }) {
        CoreStmt append;
        append.kind = kind;
        append.place = Local(3);
        append.expr = Call(tupleType, i64);
        append.org = CoreOrigin { 0, 7, CoreOriginKind::Call };
        impl.body.stmts.push_back(std::move(append));
    }

    CoreStmt retValues;
    retValues.kind = CoreStmtKind::RetValues;
    retValues.values.push_back(Int(i64, "7"));
    retValues.values.push_back(Int(i64, "8"));
    retValues.org = CoreOrigin { 0, 8, CoreOriginKind::Return };
    impl.body.stmts.push_back(std::move(retValues));

    CoreStmt retForward;
    retForward.kind = CoreStmtKind::RetForward;
    retForward.expr = Call(tupleType, i64);
    retForward.org = CoreOrigin { 0, 9, CoreOriginKind::Return };
    impl.body.stmts.push_back(std::move(retForward));

    CoreStmt returnFrom;
    returnFrom.kind = CoreStmtKind::ReturnFrom;
    returnFrom.target = 0;
    returnFrom.values.push_back(Int(i64, "9"));
    returnFrom.org = CoreOrigin { 0, 10, CoreOriginKind::Return };
    impl.body.stmts.push_back(std::move(returnFrom));

    CoreStmt returnFromForward;
    returnFromForward.kind = CoreStmtKind::ReturnFromForward;
    returnFromForward.target = 0;
    returnFromForward.expr = Call(tupleType, i64);
    returnFromForward.org = CoreOrigin { 0, 11, CoreOriginKind::Return };
    impl.body.stmts.push_back(std::move(returnFromForward));

    CoreStmt breakValue;
    breakValue.kind = CoreStmtKind::BreakValue;
    breakValue.expr = Int(i64, "10");
    breakValue.org = CoreOrigin { 0, 12, CoreOriginKind::Break };
    impl.body.stmts.push_back(std::move(breakValue));

    CoreStmt print;
    print.kind = CoreStmtKind::Print;
    print.print.push_back(Text("print"));
    print.print.push_back(ExprArg(Int(i64, "11")));
    print.print.push_back(ViewArg(i64));
    print.org = CoreOrigin { 0, 13, CoreOriginKind::Print };
    impl.body.stmts.push_back(std::move(print));

    impl.summary.reads = { CoreTarget { false, 0 } };
    impl.summary.writes = { CoreTarget { true, 0 } };
    impl.summary.grows = { CoreTarget { false, 1 } };
    impl.summary.shrinks = { CoreTarget { true, 1 } };
    impl.summary.rebinds = { CoreTarget { false, 2 } };
    impl.summary.constructs = { 0 };
    impl.summary.needs = { 0 };
    impl.summary.escapes = { 0 };
    impl.summary.aborts = true;
    impl.summary.outputs = true;
    module.impls.push_back(std::move(impl));
    CoreImpl other;
    other.name = "other";
    other.body.scope = 0;
    module.impls.push_back(std::move(other));

    module.globals.push_back(CoreGlobal {
        "first_global", i64, CoreVarKind::Var, Int(i64, "0"),
        CoreOrigin { 0, 1, CoreOriginKind::Global } });
    module.globals.push_back(CoreGlobal {
        "second_global", i64, CoreVarKind::Var, Int(i64, "0"),
        CoreOrigin { 0, 1, CoreOriginKind::Global } });

    module.targets = { CoreTargetSet { { 0, 1 } } };
    CoreContext context;
    context.impl = 0;
    context.declkey = "main";
    context.varroots = { { 5, { CoreRootRef { CoreRootRef::Static, 0 } } } };
    module.contexts.push_back(std::move(context));
    return module;
}

int main(int argc, char **argv) {
    auto constructionOrigins = ConstructionExpressionOrigins(CoreProfile::Construction);
    for (auto expr : { "[\"e_arr\",1,[[\"e_lit\",0,\"1\"]],0]",
                       "[\"e_fill\",1,[\"e_lit\",0,\"2\"],1]",
                       "[\"e_if\",[\"e_bool\",1],[\"block\",1,[],[[\"e_lit\",0,\"3\"]]],"
                       "[\"block\",2,[],[[\"e_lit\",0,\"4\"]]],2]",
                       "[\"e_block\",[\"block\",3,[],[[\"e_lit\",0,\"5\"]]],3]" })
        assert(constructionOrigins.find(expr) != string::npos);
    auto pilotOrigins = ConstructionExpressionOrigins(CoreProfile::Pilot);
    for (auto expr : { "[\"e_arr\",1,[[\"e_lit\",0,\"1\"]]]",
                       "[\"e_fill\",1,[\"e_lit\",0,\"2\"]]",
                       "[\"e_if\",[\"e_bool\",1],[\"block\",1,[],[[\"e_lit\",0,\"3\"]]],"
                       "[\"block\",2,[],[[\"e_lit\",0,\"4\"]]]]",
                       "[\"e_block\",[\"block\",3,[],[[\"e_lit\",0,\"5\"]]]]" })
        assert(pilotOrigins.find(expr) != string::npos);

    auto module = ConstructionShape();
    auto output = CoreWriter(module).Write();
    if (argc == 2 && string_view(argv[1]) == "--wire") {
        puts(output.c_str());
        return 0;
    }
    for (auto tag : { "[\"varr\",", "[\"result\",", "\"element_run\"",
                      "[\"target\",[0,1]]", "[\"r_static\"]", "[\"e_str\",", "[\"e_copy\",",
                      "[\"e_result_local\",", "[\"e_values\",", "[\"a_val\",", "[\"a_construct\",",
                      "[\"a_ref\",", "[\"s_receive\",", "[\"s_append_value\",",
                      "[\"s_append_construct\",", "[\"s_ret_values\",", "[\"s_ret_forward\",",
                      "[\"s_return_from\",", "[\"s_return_from_forward\",", "[\"s_break_value\",",
                      "[\"pa_view\",", "[\"summary\",[[\"t_param\",0]],[[\"t_global\",0]],",
                      "[[\"t_param\",1]],[[\"t_global\",1]],[[\"t_param\",2]],[0],[0],[0],1,1]",
                      "[\"struct_def\",8,[[\"field\",0,\"var\",\"mut\",0]],\"Pair<i64>\"]" })
        assert(output.find(tag) != string::npos);
    module.structs[0].displayName.clear();
    bool rejected = false;
    try {
        CoreWriter(module).Write();
    } catch (const CompileError &) {
        rejected = true;
    }
    assert(rejected);
    puts("compiler_core ok");
}
