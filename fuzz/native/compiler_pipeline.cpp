// The compiler is one translation unit: include the production driver to use
// exactly its compiler implementation while libFuzzer supplies the entry point.
#define main goose_driver_main
#include "../../src/main.cpp"
#undef main

#ifdef __linux__
#include <sys/resource.h>
#endif

#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>

enum class PipelineStage {
    Input,
    Parsed,
    Resolved,
    Typed,
    Optimized,
    BoundsChecked,
    Generated,
    Count,
};

struct PipelineMetrics {
    uint64_t inputs = 0;
    uint64_t accepted_inputs = 0;
    uint64_t compilations = 0;
    std::array<uint64_t, static_cast<size_t>(PipelineStage::Count)> stages = {};
};

static PipelineMetrics metrics;

static void PrintMetrics() {
    auto reached = [](PipelineStage stage) {
        return static_cast<unsigned long long>(metrics.stages[static_cast<size_t>(stage)]);
    };
    std::fprintf(stderr,
        "goose_pipeline_metrics inputs=%llu accepted=%llu compilations=%llu "
        "input=%llu parsed=%llu resolved=%llu typed=%llu optimized=%llu "
        "bounds_checked=%llu generated=%llu\n",
        static_cast<unsigned long long>(metrics.inputs),
        static_cast<unsigned long long>(metrics.accepted_inputs),
        static_cast<unsigned long long>(metrics.compilations),
        reached(PipelineStage::Input),
        reached(PipelineStage::Parsed),
        reached(PipelineStage::Resolved),
        reached(PipelineStage::Typed),
        reached(PipelineStage::Optimized),
        reached(PipelineStage::BoundsChecked),
        reached(PipelineStage::Generated));
}

extern "C" int LLVMFuzzerInitialize(int *, char ***) {
#ifdef __linux__
    // Every compiler phase recurses on this thread, so give it the same stack
    // allowance as the command-line compiler.
    struct rlimit limit;
    if (getrlimit(RLIMIT_STACK, &limit) != 0) abort();
    if (limit.rlim_cur < goose::COMPILERSTACK) {
        limit.rlim_cur = goose::COMPILERSTACK;
        if (setrlimit(RLIMIT_STACK, &limit) != 0) abort();
    }
#endif
    std::atexit(PrintMetrics);
    return 0;
}

struct CompileOutcome {
    bool accepted;
    std::string output;
    PipelineStage stage;
};

static CompileOutcome Compile(const std::string &source, int optlevel) {
    auto stage = PipelineStage::Input;
    try {
        // File-named shaders are the only expression form that reads a path
        // while checking. This target keeps all input effects in memory.
        if (source.find("embed_shader") != std::string::npos) return { false, {}, stage };
        goose::Ast ast;
        ast.sources.emplace_back("fuzz.goose", std::make_unique<std::string>(source));
        auto &[filename, contents] = ast.sources.back();
        goose::Parser parser(ast, filename, contents->c_str(), 0);
        parser.ParseTop();
        stage = PipelineStage::Parsed;
        // Imports name source that this hermetic target deliberately does not
        // load. The parser target still exercises their syntax and dumps.
        if (!parser.imports.empty()) return { false, {}, stage };
        goose::ResolveTypeNames(ast);
        stage = PipelineStage::Resolved;
        goose::TypeCheckProgram(ast);
        stage = PipelineStage::Typed;
        goose::Optimizer optimizer(ast, optlevel);
        stage = PipelineStage::Optimized;
        goose::BCE bce(ast);
        bce.RunAll();
        stage = PipelineStage::BoundsChecked;
        goose::CodeGen codegen(ast, {}, {});
        stage = PipelineStage::Generated;
        return { true, codegen.head + codegen.result, stage };
    } catch (const goose::CompileError &) {
        return { false, {}, stage };
    }
}

static CompileOutcome CompileMeasured(const std::string &source, int optlevel) {
    auto outcome = Compile(source, optlevel);
    metrics.compilations++;
    metrics.stages[static_cast<size_t>(outcome.stage)]++;
    return outcome;
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    // std::string owns arbitrary bytes and supplies the lexer's NUL sentinel.
    const std::string source(reinterpret_cast<const char *>(data), size);
    metrics.inputs++;
    std::array<CompileOutcome, 3> first;
    for (int optlevel = 0; optlevel < 3; optlevel++)
        first[optlevel] = CompileMeasured(source, optlevel);
    if (first[0].accepted) metrics.accepted_inputs++;
    if (first[0].accepted != first[1].accepted || first[0].accepted != first[2].accepted)
        abort();
    // Exercise both successful and rejected compilation between identical
    // inputs. Per-compilation state must not survive through either path.
    Compile(size & 1 ? "fn main() {}\n" : "fn {\n", 0);
    for (int optlevel = 0; optlevel < 3; optlevel++) {
        auto second = CompileMeasured(source, optlevel);
        if (first[optlevel].accepted != second.accepted ||
            first[optlevel].output != second.output) abort();
    }
    return 0;
}
