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
#include "../src/typecheck_flow.h"
#include "../src/typecheck_calls.h"
#include "../src/typecheck_builtins.h"
#include "../src/typecheck_nodes.h"
#include "../src/optimize.h"
#include "../src/optimize_basecase.h"
#include "../src/optimize_tre.h"
#include "../src/optimize_loops.h"
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
#include "../src/units/postpass.h"
#include "../src/report/report.h"
#include "../src/units/share_report.h"
#include "../src/report/deps_report.h"
#include "../src/progress.h"
#include "../src/process.h"
#include "../src/buildfile.h"
#include "../src/toolchain.h"
#include "../src/build.h"
#include "../src/json.h"
#include "../src/units/build.h"

using namespace goose;

extern "C" gs_shaderc_result gs_shaderc_compile(const char *, const char *, int) {
    return { nullptr, 0, nullptr };
}

extern "C" void gs_shaderc_free(gs_shaderc_result *) {}

struct BuiltProgram {
    UnitContract contract;
    UnitsBuildReport report;
    ProcessResult run;
};

static UnitContractValues ContractValues() {
    UnitContractValues values;
    values.goose_digest = string(64, 'a');
    values.runtime_version = "runtime-a";
    values.args = { "-O2" };
    values.c_compiler_digest = string(64, 'b');
    values.c_compiler_version = "17.1";
    values.c_compiler_name = "cc";
    values.c_compiler_style = "cc";
    values.c_flags = { "-O2", "-DUNIT_VALUE=7" };
    values.system_libs = { "-lm", "-pthread" };
    values.target = UnitHostTarget();
    values.environment = { { "GOOSE_STDLIB", "" }, { "GOOSE_CC", "" },
                           { "GOOSE_RUNTIME", "" } };
    return values;
}

static vector<pair<string, string>> UnitSources() {
    return {
        { "main.c", "#include \"goose_runtime.h\"\nint unit_value(void);\n"
                    "int main(void) { return unit_value() - 7; }\n" },
        { "value.c", "#include \"goose_runtime.h\"\nint unit_value(void) { return UNIT_VALUE; }\n" },
        { "extra.c", "#include \"goose_runtime.h\"\nint extra_value(void) { return UNIT_VALUE; }\n" },
    };
}

static BuiltProgram BuildProgram(const string &builddir, const string &exe,
                                 const UnitContractValues &values,
                                 const vector<pair<string, string>> &sources) {
    BuiltProgram result;
    result.contract = MakeContract(values);
    UnitsBuildInput in;
    Toolchain tc;
    tc.cc = FindOnPath("cc");
    tc.style = "cc";
    BuildOptions opts;
    in.tc = &tc;
    in.opts = &opts;
    in.contract = result.contract;
    in.store.dir = UnitStoreDirectory(builddir, result.contract);
    in.exe = exe;
    in.verify = true;
    in.msgs = stderr;
    filesystem::create_directories(filesystem::path(in.store.Units()));
    assert(UnitWriteFile(in.store.Units() + "/goose_runtime.h", "\n"));
    unit_stats.files = sources;
    for (auto &[name, text] : sources)
        assert(UnitWriteFile(in.store.Units() + "/" + name, text));
    units_build = UnitsBuildReport();
    assert(BuildUnitObjects(in, "") == 0);
    result.report = units_build;
    result.run = RunProcess({ exe });
    return result;
}

static map<string, string> StoreSnapshot(const string &store) {
    map<string, string> snapshot;
    for (auto &entry : filesystem::recursive_directory_iterator(filesystem::path(store))) {
        if (!entry.is_regular_file()) continue;
        string text;
        assert(UnitReadFile(entry.path().string(), text));
        snapshot[filesystem::relative(entry.path(), filesystem::path(store)).string()] = text;
    }
    return snapshot;
}

static size_t InvocationUnits(const vector<UnitsBuildReport::Invocation> &invs) {
    size_t count = 0;
    for (auto &inv : invs) count += inv.units.size();
    return count;
}

static void TestContractVariantBuildsItsOwnWarmStore(
    const string &builddir, const string &exe,
    const vector<pair<string, string>> &sources,
    const UnitContractValues &base_values, const UnitContractValues &variant_values,
    int variant_exit) {
    auto base = BuildProgram(builddir, exe, base_values, sources);
    assert(base.run.started && base.run.code == 0);
    assert(base.report.units_written == (long long)sources.size());
    assert(base.report.reused == 0 && base.report.missed == (long long)sources.size());
    assert(InvocationUnits(base.report.compiles) == sources.size());
    auto base_snapshot = StoreSnapshot(UnitStoreDirectory(builddir, base.contract));

    auto variant = BuildProgram(builddir, exe, variant_values, sources);
    assert(variant.contract.digest != base.contract.digest);
    assert(UnitStoreDirectory(builddir, variant.contract) !=
           UnitStoreDirectory(builddir, base.contract));
    assert(variant.run.started && variant.run.code == variant_exit);
    assert(variant.report.units_written == (long long)sources.size());
    assert(variant.report.reused == 0 && variant.report.missed == (long long)sources.size());
    assert(InvocationUnits(variant.report.compiles) == sources.size());
    assert(StoreSnapshot(UnitStoreDirectory(builddir, base.contract)) == base_snapshot);
    auto variant_snapshot = StoreSnapshot(UnitStoreDirectory(builddir, variant.contract));

    auto base_back = BuildProgram(builddir, exe, base_values, sources);
    assert(base_back.run.started && base_back.run.code == 0);
    assert(base_back.report.reused == (long long)sources.size() && base_back.report.missed == 0);
    assert(base_back.report.compiles.empty());
    assert(InvocationUnits(base_back.report.verification) == sources.size());
    assert(StoreSnapshot(UnitStoreDirectory(builddir, variant.contract)) == variant_snapshot);

    auto variant_back = BuildProgram(builddir, exe, variant_values, sources);
    assert(variant_back.run.started && variant_back.run.code == variant_exit);
    assert(variant_back.report.reused == (long long)sources.size() && variant_back.report.missed == 0);
    assert(variant_back.report.compiles.empty());
    assert(InvocationUnits(variant_back.report.verification) == sources.size());
    assert(StoreSnapshot(UnitStoreDirectory(builddir, base.contract)) == base_snapshot);
}

static void TestNativeUnitBuilderContractDimensions() {
    auto root = AbsolutePath(".work/tmp/compiler_units_builder");
    std::error_code ec;
    filesystem::remove_all(filesystem::path(root), ec);
    assert(!ec);
    filesystem::create_directories(filesystem::path(root), ec);
    assert(!ec);
    auto sources = UnitSources();
    auto base_values = ContractValues();

    auto c_flags = base_values;
    c_flags.c_flags[1] = "-DUNIT_VALUE=8";
    TestContractVariantBuildsItsOwnWarmStore(root + "/c-flags", root + "/c-flags/program",
                                             sources, base_values, c_flags, 1);

    auto target = base_values;
    target.target.arch = "test-target";
    TestContractVariantBuildsItsOwnWarmStore(root + "/target", root + "/target/program",
                                             sources, base_values, target, 0);

    auto runtime = base_values;
    runtime.runtime_version = "runtime-b";
    TestContractVariantBuildsItsOwnWarmStore(root + "/runtime", root + "/runtime/program",
                                             sources, base_values, runtime, 0);
    filesystem::remove_all(filesystem::path(root), ec);
    assert(!ec);
}

int main() {
    TestNativeUnitBuilderContractDimensions();
}
