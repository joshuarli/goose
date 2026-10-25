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
#include "../src/optimize_reassoc.h"
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
#include "../src/units/emit.h"
#include "../src/report/report.h"
#include "../src/units/share_report.h"
#include "../src/report/deps_report.h"
#include "../src/progress.h"
#include "../src/process.h"
#include "../src/json.h"
#include "../src/buildfile.h"
#include "../src/toolchain.h"
#include "../src/builtin.h"
#include "../src/build.h"
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

static void TestLinkResponseProbes(const string &root) {
    auto dir = root + "/link-response";
    std::error_code ec;
    filesystem::create_directories(filesystem::path(dir), ec);
    assert(!ec);
    auto present = dir + "/present.a";
    auto absent = dir + "/absent.a";
    auto response = dir + "/link-cc.rsp";
    assert(UnitWriteFile(present, ""));
    assert(UnitWriteFile(response, "present.a\nabsent.a\n"));

    RecordedInputs inputs;
    auto previous = input_recorder;
    input_recorder = &inputs;
    auto output = AbsoluteLinkFile(response, "units-builder-probes", "cc");
    input_recorder = previous;

    auto recorded = inputs.Text();
    assert(recorded.find(cat("P\t\t", present, "\n")) != string::npos);
    assert(recorded.find(cat("A\t\t", absent, "\n")) != string::npos);
    string text;
    assert(UnitReadFile(output, text));
    assert(text == cat(present, "\n", "absent.a\n"));
}

static string RuntimeVersionOf(const string &goose) {
    auto result = RunProcess({ goose, "version" });
    assert(result.started && result.code == 0);
    auto end = result.output.find_first_of("\r\n");
    auto line = result.output.substr(0, end);
    const string prefix = " (runtime ";
    auto start = line.rfind(prefix);
    assert(line.starts_with("goose ") && start != string::npos && line.ends_with(")"));
    return line.substr(start + prefix.size(), line.size() - start - prefix.size() - 1);
}

static UnitContractValues SourceContractValues(const string &goose, const Toolchain &tc,
                                               const BuildOptions &opts) {
    UnitContractValues values;
    values.goose_digest = UnitBinaryDigest(goose);
    values.runtime_version = RuntimeVersionOf(goose);
    values.args = { "--standalone", "-O1" };
    values.c_compiler_digest = UnitBinaryDigest(tc.cc);
    values.c_compiler_version = tc.version;
    values.c_compiler_name = tc.name;
    values.c_compiler_style = tc.style;
    Builder builder { tc, opts, stderr };
    values.c_flags = builder.CFlags();
    values.system_libs = builder.SystemLibs();
    values.target = UnitHostTarget();
    for (auto name : { "GOOSE_STDLIB", "GOOSE_CC", "GOOSE_RUNTIME" }) {
        auto value = getenv(name);
        values.environment.push_back({ name, value ? value : "" });
    }
    return values;
}

static vector<pair<string, string>> ReadEmittedUnits(const string &dir, const string &store) {
    vector<pair<string, string>> sources;
    string runtime_header;
    for (auto &entry : filesystem::directory_iterator(filesystem::path(dir))) {
        if (!entry.is_regular_file()) continue;
        auto name = entry.path().filename().string();
        string text;
        assert(UnitReadFile(entry.path().string(), text));
        if (name == "goose_runtime.h") runtime_header = std::move(text);
        else if (name.size() >= 2 && name.compare(name.size() - 2, 2, ".c") == 0) {
            assert(UnitWriteFile(store + "/" + name, text));
            sources.emplace_back(name, std::move(text));
        }
    }
    assert(!runtime_header.empty() && !sources.empty());
    assert(UnitWriteFile(store + "/goose_runtime.h", runtime_header));
    return sources;
}

static ProcessResult BuildCleanSource(const string &goose, const string &source,
                                      const string &cfile, const string &exe,
                                      const Toolchain &tc, const vector<string> &c_flags,
                                      const vector<string> &system_libs, const string &cwd) {
    auto emit = RunProcess({ goose, "--standalone", "-O1", "-o", cfile, source }, cwd);
    assert(emit.started && emit.code == 0);
    vector<string> command = { tc.cc };
    for (auto &flag : c_flags) command.push_back(flag);
    if (tc.style == "msvc") {
        command.push_back(cfile);
        command.push_back(cat("/Fe:", exe));
    } else {
        command.push_back(cfile);
        command.push_back("-o");
        command.push_back(exe);
        for (auto &library : system_libs) command.push_back(library);
    }
    auto compile = RunProcess(command, cwd);
    assert(compile.started && compile.code == 0);
    return RunProcess({ exe }, cwd);
}

static BuiltProgram BuildEmittedSource(const string &goose, const string &emitted_dir,
                                       const string &builddir, const string &exe,
                                       const UnitContractValues &values, const Toolchain &tc,
                                       const BuildOptions &opts) {
    BuiltProgram result;
    result.contract = MakeContract(values);
    UnitsBuildInput in;
    in.tc = &tc;
    in.opts = &opts;
    in.contract = result.contract;
    in.store.dir = UnitStoreDirectory(builddir, result.contract);
    in.exe = exe;
    in.verify = true;
    in.msgs = stderr;
    std::error_code ec;
    filesystem::create_directories(filesystem::path(in.store.Units()), ec);
    assert(!ec);
    unit_stats.files = ReadEmittedUnits(emitted_dir, in.store.Units());
    units_build = UnitsBuildReport();
    assert(BuildUnitObjects(in, "") == 0);
    result.report = units_build;
    result.run = RunProcess({ exe });
    return result;
}

static void TestEmittedSourceContractVariant(
    const char *dimension, const string &goose, const string &emitted_dir,
    const string &builddir, const string &exe, const UnitContractValues &base_values,
    const UnitContractValues &variant_values, const Toolchain &tc, const BuildOptions &opts,
    const ProcessResult &expected_run, size_t unit_count,
    const map<string, string> &base_snapshot) {
    auto base_contract = MakeContract(base_values);
    auto variant_contract = MakeContract(variant_values);
    assert(variant_contract.digest != base_contract.digest);
    assert(UnitStoreDirectory(builddir, variant_contract) !=
           UnitStoreDirectory(builddir, base_contract));

    auto variant = BuildEmittedSource(goose, emitted_dir, builddir, exe,
                                      variant_values, tc, opts);
    assert(variant.run.started && variant.run.code == expected_run.code &&
           variant.run.output == expected_run.output);
    assert(variant.report.units_written == (long long)unit_count &&
           variant.report.missed == (long long)unit_count && variant.report.reused == 0 &&
           InvocationUnits(variant.report.compiles) == unit_count);
    assert(StoreSnapshot(UnitStoreDirectory(builddir, base_contract)) == base_snapshot);
    auto variant_snapshot = StoreSnapshot(UnitStoreDirectory(builddir, variant_contract));

    auto base_back = BuildEmittedSource(goose, emitted_dir, builddir, exe,
                                        base_values, tc, opts);
    assert(base_back.run.started && base_back.run.code == expected_run.code &&
           base_back.run.output == expected_run.output);
    assert(base_back.report.reused == (long long)unit_count && base_back.report.missed == 0 &&
           base_back.report.compiles.empty() &&
           InvocationUnits(base_back.report.verification) == unit_count);
    assert(StoreSnapshot(UnitStoreDirectory(builddir, variant_contract)) == variant_snapshot);

    auto variant_back = BuildEmittedSource(goose, emitted_dir, builddir, exe,
                                           variant_values, tc, opts);
    assert(variant_back.run.started && variant_back.run.code == expected_run.code &&
           variant_back.run.output == expected_run.output);
    assert(variant_back.report.reused == (long long)unit_count && variant_back.report.missed == 0 &&
           variant_back.report.compiles.empty() &&
           InvocationUnits(variant_back.report.verification) == unit_count);
    assert(StoreSnapshot(UnitStoreDirectory(builddir, base_contract)) == base_snapshot);
    fprintf(stderr, "compiler_units_builder: %s emitted-source probe passed\n", dimension);
}

static void TestEmittedSourceUnitBuilder(const string &goose, const string &source) {
    auto root = AbsolutePath(".work/tmp/compiler_units_emitted");
    std::error_code ec;
    filesystem::remove_all(filesystem::path(root), ec);
    assert(!ec);
    filesystem::create_directories(filesystem::path(root), ec);
    assert(!ec);
    SetEnvVar("GOOSE_HOME", root + "/goose-home");
    filesystem::create_directories(filesystem::path(GooseHome()), ec);
    assert(!ec);
    TestLinkResponseProbes(root);

    auto report_path = root + "/build-report.json";
    auto reported_build = RunProcess({ goose, "build", "--units", "--standalone", "-O1",
        "--build-report", report_path, "-o", root + "/reported", source }, root);
    assert(reported_build.started && reported_build.code == 0);
    string report_text;
    assert(UnitReadFile(report_path, report_text));
    auto report = ParseJson(report_text);
    auto phases = report.Get("phases");
    assert(phases);
    auto native_phase = phases->Get("native_build");
    assert(native_phase);
    auto native_wall = native_phase->Get("wall_seconds");
    assert(native_wall && native_wall->kind == Json::NUMBER);
    auto native = report.Get("extensions")->Get("native_compile");
    assert(native && !native->Arr("native_compiler_invocations").empty());
    for (auto &invocation : native->Arr("native_compiler_invocations"))
        assert(native_wall->num >= invocation.Get("wall_seconds")->num);
    assert(native_wall->num >= native->Get("link")->Get("wall_seconds")->num);
    auto frontend = native->Arr("frontend_phases");
    assert(any_of(frontend.begin(), frontend.end(), [](const Json &phase) { return phase.str == "write_output"; }));
    assert(none_of(frontend.begin(), frontend.end(), [](const Json &phase) { return phase.str == "native_build"; }));

    Toolchain tc;
    string why;
    assert(FindToolchain("", tc, why));
    BuildOptions opts;
    opts.standalone = true;
    auto base_values = SourceContractValues(goose, tc, opts);
    auto variant_values = base_values;
    variant_values.c_flags.push_back(tc.style == "msvc" ? "/Oy-" : "-fno-omit-frame-pointer");

    auto emitted_dir = root + "/emitted";
    auto emitted = RunProcess({ goose, "--standalone", "-O1", "--emit-units", emitted_dir, source }, root);
    assert(emitted.started && emitted.code == 0);
    auto clean_base = BuildCleanSource(goose, source, root + "/clean-base.c", root + "/clean-base",
                                       tc, base_values.c_flags, base_values.system_libs, root);
    auto clean_variant = BuildCleanSource(goose, source, root + "/clean-variant.c", root + "/clean-variant",
                                          tc, variant_values.c_flags, variant_values.system_libs, root);
    assert(clean_base.started && clean_base.code == 0 && clean_variant.started &&
           clean_variant.code == 0 && clean_base.output == clean_variant.output);

    #ifdef _WIN32
        auto suffix = string(".exe");
    #else
        auto suffix = string();
    #endif
    auto program = root + "/program" + suffix;
    auto base = BuildEmittedSource(goose, emitted_dir, root, program, base_values, tc, opts);
    assert(base.run.started && base.run.code == clean_base.code && base.run.output == clean_base.output);
    auto unit_count = (size_t)base.report.units_written;
    assert(unit_count > 0 && base.report.missed == (long long)unit_count &&
           base.report.reused == 0 && InvocationUnits(base.report.compiles) == unit_count);
    auto base_snapshot = StoreSnapshot(UnitStoreDirectory(root, base.contract));

    TestEmittedSourceContractVariant("raw C flags", goose, emitted_dir, root, program,
                                    base_values, variant_values, tc, opts, clean_variant,
                                    unit_count, base_snapshot);

    auto target_values = base_values;
    target_values.target.arch = "builder-boundary-target";
    TestEmittedSourceContractVariant("target identity", goose, emitted_dir, root, program,
                                    base_values, target_values, tc, opts, clean_base,
                                    unit_count, base_snapshot);

    auto runtime_values = base_values;
    runtime_values.runtime_version += "-builder-boundary";
    TestEmittedSourceContractVariant("runtime identity", goose, emitted_dir, root, program,
                                    base_values, runtime_values, tc, opts, clean_base,
                                    unit_count, base_snapshot);

    filesystem::remove_all(filesystem::path(root), ec);
    assert(!ec);
}

static void TestSharedProgramSupport() {
    auto root = AbsolutePath(".work/tmp/compiler_units_support");
    std::error_code ec;
    filesystem::remove_all(root, ec);
    assert(!ec);
    filesystem::create_directories(root, ec);
    assert(!ec);
    UnitSource source;
    source.support.Type("typedef struct { uint8_t tag; int64_t amount; } support_argument;\n");
    source.support.State("GS_TLS int64_t support_total;\n");
    source.support.Function("int64_t support_add(support_argument argument)",
                            "{ support_total += argument.tag == 1 ? argument.amount : 1000; return support_total; }\n");
    source.support.Function("int64_t support_finish(void)",
                            "{ int64_t total = support_total; support_total = 0; return total; }\n");
    source.gblock = "    int64_t total_at_init;\n";
    source.globals.push_back({ "globals_module", { "GS_GL->total_at_init" }, "GS_GL->total_at_init" });
    source.segmodules = { "globals_module" };
    source.unitinits = { { "globals_module", "initialize" } };
    source.code = "static void initialize(void) {\n"
                  "    GS_GL->total_at_init = support_add((support_argument){ 1, 2 });\n}\n"
                  "static int64_t first(void) {\n"
                  "    return support_add((support_argument){ 1, 3 });\n}\n"
                  "static int64_t second(void) {\n"
                  "    return support_add((support_argument){ 1, 4 });\n}\n"
                  "int main(void) {\n"
                  "    segment_globals_module = &segment_globals_module_main;\n"
                  "    initialize();\n"
                  "    int64_t a = first();\n"
                  "    int64_t b = second();\n"
                  "    int64_t end = support_finish();\n"
                  "    printf(\"%lld %lld %lld %lld\\n\", (long long)GS_GL->total_at_init, (long long)a, (long long)b, (long long)end);\n"
                  "    if (support_total != 0) return 1;\n"
                  "    return 0;\n}\n";
    source.functions["first"] = { "first_module", nullptr };
    source.functions["second"] = { "second_module", nullptr };
    source.fail = [](const string &message) { throw CompileError { message }; };
    source.segname = [](const string &module) { return "segment_" + module; };
    UnitInputs input;
    input.runtime_header = "#ifndef GOOSE_RUNTIME_H\n#define GOOSE_RUNTIME_H\n"
                           "#include <stdint.h>\n#include <stdio.h>\n"
                           "#define GS_TLS _Thread_local\n#define GS_HIDDEN\n"
                           "typedef struct { int unused; } gs_stack;\n";
    WriteUnits(source, root + "/units", input);
    Toolchain tc;
    string why;
    assert(FindToolchain("", tc, why));
    auto header = "#include <stdint.h>\n#include <stdio.h>\n"
                  "#define GS_TLS _Thread_local\n";
    assert(UnitWriteFile(root + "/single.c", cat(header, source.support.single,
                         "static int64_t global_total_at_init;\n",
                         UnitReplace(UnitReplace(source.code, "    segment_globals_module = &segment_globals_module_main;\n", ""), "GS_GL->", "global_"))));
    for (auto optimization : { "-O0", "-O2" }) {
        vector<string> command = { tc.cc, optimization };
        for (auto &unit : unit_stats.units) command.push_back(root + "/units/" + unit.file);
        command.insert(command.end(), { "-o", root + "/support" });
        auto compile = RunProcess(command, root);
        if (!compile.started || compile.code) fputs(compile.output.c_str(), stderr);
        assert(compile.started && compile.code == 0);
        auto run = RunProcess({ root + "/support" }, root);
        assert(run.started && run.code == 0 && run.output == "2 5 9 9\n");
        auto single_compile = RunProcess({ tc.cc, optimization, root + "/single.c", "-o", root + "/single" }, root);
        assert(single_compile.started && single_compile.code == 0);
        auto single_run = RunProcess({ root + "/single" }, root);
        assert(single_run.started && single_run.code == run.code && single_run.output == run.output);
    }
    filesystem::remove_all(root, ec);
    assert(!ec);
}

int main(int argc, char **argv) {
    TestSharedProgramSupport();
    TestNativeUnitBuilderContractDimensions();
    assert(argc == 1 || argc == 3);
    if (argc == 3) TestEmittedSourceUnitBuilder(argv[1], argv[2]);
}
