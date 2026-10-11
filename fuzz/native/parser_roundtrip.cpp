// The compiler is one translation unit: its AST virtuals need every pass's
// definitions even when this target only parses and dumps. Rename the driver
// entry point so libFuzzer supplies main, with the same header order as goose.
#define main goose_driver_main
#include "../../src/main.cpp"
#undef main

#ifdef __linux__
#include <sys/resource.h>
#endif

extern "C" int LLVMFuzzerInitialize(int *, char ***) {
#ifdef __linux__
    // Parsing recurses on the calling thread; match the compiler's stack
    // reserve so ordinary nested inputs get the same native headroom.
    struct rlimit limit;
    if (getrlimit(RLIMIT_STACK, &limit) != 0) abort();
    if (limit.rlim_cur < goose::COMPILERSTACK) {
        limit.rlim_cur = goose::COMPILERSTACK;
        if (setrlimit(RLIMIT_STACK, &limit) != 0) abort();
    }
#endif
    return 0;
}

static std::string ParseAndDump(const std::string &source) {
    goose::Ast ast;
    ast.sources.emplace_back("fuzz.goose", std::make_unique<std::string>(source));
    auto &[filename, contents] = ast.sources.back();
    goose::Parser parser(ast, filename, contents->c_str(), 0);
    parser.ParseTop();
    std::string dump;
    ast.Dump(dump);
    return dump;
}

extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
    // std::string owns arbitrary bytes and supplies the lexer's NUL sentinel.
    const std::string source(reinterpret_cast<const char *>(data), size);
    std::string first;
    try {
        first = ParseAndDump(source);
    } catch (const goose::CompileError &) {
        return 0;
    }
    try {
        if (ParseAndDump(first) != first) abort();
    } catch (const goose::CompileError &) {
        // A successful parse must dump a program the same parser accepts.
        abort();
    }
    return 0;
}
