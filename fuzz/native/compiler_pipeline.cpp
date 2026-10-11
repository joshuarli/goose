// The compiler is one translation unit: include the production driver to use
// exactly its compiler implementation while libFuzzer supplies the entry point.
#define main goose_driver_main
#include "../../src/main.cpp"
#undef main

#ifdef __linux__
#include <sys/resource.h>
#endif

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
    return 0;
}

struct CompileOutcome {
    bool accepted;
    std::string output;
};

static CompileOutcome Compile(const std::string &source, int optlevel) {
    try {
        // File-named shaders are the only expression form that reads a path
        // while checking. This target keeps all input effects in memory.
        if (source.find("embed_shader") != std::string::npos) return { false, {} };
        goose::Ast ast;
        ast.sources.emplace_back("fuzz.goose", std::make_unique<std::string>(source));
        auto &[filename, contents] = ast.sources.back();
        goose::Parser parser(ast, filename, contents->c_str(), 0);
        parser.ParseTop();
        // Imports name source that this hermetic target deliberately does not
        // load. The parser target still exercises their syntax and dumps.
        if (!parser.imports.empty()) return { false, {} };
        goose::ResolveTypeNames(ast);
        goose::TypeCheckProgram(ast);
        goose::Optimizer optimizer(ast, optlevel);
        goose::BCE bce(ast);
        bce.RunAll();
        goose::CodeGen codegen(ast, {}, {});
        return { true, codegen.head + codegen.result };
    } catch (const goose::CompileError &) {
        return { false, {} };
    }
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    // std::string owns arbitrary bytes and supplies the lexer's NUL sentinel.
    const std::string source(reinterpret_cast<const char *>(data), size);
    const int optlevel = size ? data[0] % 3 : 0;
    auto first = Compile(source, optlevel);
    // Exercise both successful and rejected compilation between identical
    // inputs. Per-compilation state must not survive through either path.
    Compile(size & 1 ? "fn main() {}\n" : "fn {\n", (optlevel + 1) % 3);
    auto second = Compile(source, optlevel);
    if (first.accepted != second.accepted || first.output != second.output) abort();
    return 0;
}
