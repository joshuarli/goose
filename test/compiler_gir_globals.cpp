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

enum class GlobalValue { Integer, Boolean, FixedArray, PackedStruct };

CoreExprP Integer(CoreTypeId type, const char *value) {
    auto expression = make_unique<CoreExpr>();
    expression->kind = CoreExprKind::Lit;
    expression->type = type;
    expression->value = value;
    return expression;
}

CoreModule GlobalModule(CoreProfile profile, GlobalValue value) {
    CoreModule core;
    core.profile = profile;
    core.files = { "global-initializer.goose" };
    auto i64 = core.IntType(CoreIntTy::I64);
    auto type = i64;
    auto expression = Integer(i64, "41");
    if (value == GlobalValue::Boolean) {
        type = core.BoolType();
        expression->kind = CoreExprKind::Bool;
        expression->type = type;
        expression->flag = true;
    } else if (value == GlobalValue::FixedArray) {
        type = core.Intern(CoreType { .kind = CoreType::Arr, .elem = i64, .count = 2 });
        expression->kind = CoreExprKind::Arr;
        expression->type = type;
        expression->elems.push_back(Integer(i64, "7"));
        expression->elems.push_back(Integer(i64, "11"));
    } else if (value == GlobalValue::PackedStruct) {
        auto u8 = core.IntType(CoreIntTy::U8);
        core.structs = { CoreStruct { 9, {
            CoreField { u8, CoreVarKind::Let, CoreMut::Const, 0 },
            CoreField { i64, CoreVarKind::Let, CoreMut::Const, 1 }
        }, "Packed" } };
        type = core.Intern(CoreType { .kind = CoreType::Struct, .structid = 0 });
        expression->kind = CoreExprKind::Struct;
        expression->type = type;
        expression->elems.push_back(Integer(u8, "3"));
        expression->elems.push_back(Integer(i64, "13"));
    }
    auto origin = CoreOrigin { 0, 1, CoreOriginKind::Let };
    core.globals.push_back(CoreGlobal { "value", type, CoreVarKind::Let, std::move(expression), origin });
    CoreImpl entry;
    entry.name = "main";
    entry.body.scope = 0;
    entry.summary.unknown = true;
    core.impls.push_back(std::move(entry));
    CoreImpl regular;
    regular.name = "regular-scalar-return";
    regular.results = { CoreResultDescriptor { i64, CoreRequest::Register } };
    regular.body.scope = 0;
    regular.summary.unknown = true;
    CoreStmt returned;
    returned.kind = CoreStmtKind::Ret;
    returned.expr = Integer(i64, "17");
    returned.org = origin;
    regular.body.stmts.push_back(std::move(returned));
    core.impls.push_back(std::move(regular));
    core.contexts = { CoreContext { .impl = 0 }, CoreContext { .impl = 1 } };
    core.entry = 0;
    return core;
}

void Valid(GirModule &module) {
    auto violation = GirVerifier(module).Verify();
    if (violation) fprintf(stderr, "%s: %s\n", violation->code.c_str(), violation->message.c_str());
    assert(!violation);
}

void GlobalInitializersConsumeResults(CoreProfile profile, GlobalValue value) {
    auto core = GlobalModule(profile, value);
    auto high = GirLowerer(core, core.files, { CoreOrigin { 0, 1, CoreOriginKind::Let } },
                           [](const CoreOrigin &) { return 0; }).Lower();
    Valid(high);
    auto low = GirToLow(high).Lower();
    Valid(low);
    auto &initializer = low.funcs[low.initfuncs[0]];
    assert(initializer.params.size() == 1);
    assert(low.Type(initializer.params[0]).kind == CoreType::Int);
    assert(low.Type(initializer.params[0]).ity == CoreIntTy::I64);
    assert(initializer.results.empty());
    if (profile != CoreProfile::Construction) {
        assert(low.funcs[1].results.size() == 1);
        assert(low.Type(low.funcs[1].results[0]).ity == CoreIntTy::I64);
    }
    for (auto &block : initializer.blocks) for (auto &instruction : block.insts)
        if (instruction.op == GirOp::Ret) assert(instruction.vals.empty());
    if (profile == CoreProfile::Shrink && value == GlobalValue::Integer) {
        auto bad = low;
        auto &function = bad.funcs[bad.initfuncs[0]];
        int result = 0;
        for (auto &block : function.blocks) {
            result += (int)block.params.size();
            for (auto &instruction : block.insts) result += GirDefinesValue(instruction);
        }
        auto &instructions = function.blocks.back().insts;
        GirInst constant;
        constant.op = GirOp::Int;
        constant.res = result;
        constant.ty = bad.IntType(CoreIntTy::I64);
        constant.text = "99";
        instructions.insert(instructions.end() - 1, constant);
        instructions.back().vals = { result };
        auto violation = GirVerifier(bad).Verify();
        assert(violation && violation->code == "GIR-V010");
        auto stale = low;
        stale.funcs[stale.initfuncs[0]].results = { stale.IntType(CoreIntTy::I64) };
        violation = GirVerifier(stale).Verify();
        assert(violation && violation->code == "GIR-V010");
    }
}

}

int main() {
    for (auto profile : { CoreProfile::Shrink, CoreProfile::Pilot, CoreProfile::Construction })
        for (auto value : { GlobalValue::Integer, GlobalValue::Boolean, GlobalValue::FixedArray, GlobalValue::PackedStruct }) {
            if (profile == CoreProfile::Pilot && value == GlobalValue::PackedStruct) continue;
            GlobalInitializersConsumeResults(profile, value);
        }
    printf("compiler_gir_globals ok\n");
}
