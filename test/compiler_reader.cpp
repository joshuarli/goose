#ifdef NDEBUG
#undef NDEBUG
#endif
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <iterator>
#include <sstream>
#include <string>
#include <vector>

namespace fs = std::filesystem;
using std::string;
using std::vector;

struct Allowed {
    const char *file;
    const char *text;
    const char *why;
    int used = 0;
};

static bool word_before(const string &line, size_t at) {
    if (at == 0) return false;
    auto c = line[at - 1];
    return isalnum((unsigned char)c) || c == '_';
}

static string code_without_comments_or_literals(const string &source) {
    auto code = source;
    auto blank = [&](size_t index) {
        if (code[index] != '\n' && code[index] != '\r') code[index] = ' ';
    };
    for (size_t i = 0; i < source.size();) {
        if (source[i] == '/' && i + 1 < source.size() && source[i + 1] == '/') {
            while (i < source.size() && source[i] != '\n') blank(i++);
            continue;
        }
        if (source[i] == '/' && i + 1 < source.size() && source[i + 1] == '*') {
            blank(i++);
            blank(i++);
            while (i < source.size()) {
                if (source[i] == '*' && i + 1 < source.size() && source[i + 1] == '/') {
                    blank(i++);
                    blank(i++);
                    break;
                }
                blank(i++);
            }
            continue;
        }
        if (source[i] == 'R' && i + 1 < source.size() && source[i + 1] == '"') {
            auto delimiterStart = i + 2;
            auto open = delimiterStart;
            while (open < source.size() && source[open] != '(' && open - delimiterStart <= 16 &&
                   source[open] != ' ' && source[open] != '\t' && source[open] != '\n' &&
                   source[open] != '\r' && source[open] != '\\' && source[open] != ')')
                open++;
            if (open < source.size() && source[open] == '(' && open - delimiterStart <= 16) {
                auto closeToken = ")" + source.substr(delimiterStart, open - delimiterStart) + "\"";
                auto close = source.find(closeToken, open + 1);
                auto end = close == string::npos ? source.size() : close + closeToken.size();
                while (i < end) blank(i++);
                continue;
            }
        }
        if (source[i] == '"' || source[i] == '\'') {
            auto quote = source[i];
            blank(i++);
            auto escaped = false;
            while (i < source.size()) {
                auto current = source[i];
                blank(i++);
                if (escaped) escaped = false;
                else if (current == '\\') escaped = true;
                else if (current == quote) break;
            }
            continue;
        }
        i++;
    }
    return code;
}

static bool has_file_access_pattern(const string &code) {
    static const vector<string> patterns = { "fopen(", "ifstream", "fstream", "filesystem::exists",
        "filesystem::is_directory", "filesystem::is_regular_file", "directory_iterator",
        "filesystem::file_size", "filesystem::last_write_time", "filesystem::status",
        "filesystem::canonical", "opendir", "readdir", "fread(", "getenv(", "stat(", "access(" };
    for (auto &pattern : patterns) {
        auto at = code.find(pattern);
        while (at != string::npos) {
            if ((pattern != "stat(" && pattern != "access(") || !word_before(code, at)) return true;
            at = code.find(pattern, at + 1);
        }
    }
    return false;
}

static const char *skipped[] = {
    "build.h",
    "toolchain.h",
    "jit.h",
    "runtime_inline.h",
    "lint_facts.h",
    "units/build.h",
    "process.cpp",
    "core/",
};

static vector<Allowed> allowed = {
    { "utils.h", "fopen(path.c_str(), \"rb\")", "LoadFile, the reader" },
    { "utils.h", "fread(dest.data()", "LoadFile, the reader" },
    { "utils.h", "std::filesystem::is_directory", "ProbeDirectory, the reader" },
    { "main.cpp", "auto f = fopen(path.c_str(), \"rb\");", "FileExists, the reader, and the linter's private file" },
    { "main.cpp", "fread(buf, 1, sizeof buf, f)", "the linter's private facts file" },
    { "main.cpp", "fopen(path.c_str(), \"wb\")", "writes" },
    { "main.cpp", "fopen(path, \"wb\")", "writes" },
    { "main.cpp", "fopen(dumpfile.c_str(), \"wb\")", "writes" },
    { "main.cpp", "fopen(outfile.c_str(), \"wb\")", "writes" },
    { "report.h", "fopen(r.path.c_str(), \"wb\")", "writes" },
    { "emit.h", "fopen(path.c_str(), \"wb\")", "writes the units" },
    { "main.cpp", "filesystem::directory_iterator(", "a --verify-reuse hit comparing the store's own units" },
    { "main.cpp", "getenv(\"GOOSE_STDLIB\")", "named in the contract" },
    { "main.cpp", "getenv(\"GOOSE_RUNTIME\")", "named in the contract; the runtime's source search" },
    { "native.h", "directory_iterator it(dir, ec)", "the native build's nested package discovery, which a build with such a part does not skip" },
    { "native.h", "recursive_directory_iterator", "the native build's inputs, which a build with such a part does not skip" },
    { "native.h", "directory_iterator it(filesystem::path(replydir)", "the native build's cmake reply" },
    { "native.h", "filesystem::file_size(filesystem::path(p), sec)", "the native build's freshness hash, which a build with such a part does not skip" },
    { "native.h", "last_write_time", "the native build's freshness" },
    { "packages.h", "filesystem::exists(p, ec)", "removing a cached checkout" },
    { "packages.h", "recursive_directory_iterator it(p, ec)", "removing a cached checkout" },
    { "lsp_rpc.h", "fread(body.data(), 1, length, in)", "the language server transport reads stdin, not a compilation input" },
    { "progress.cpp", "getenv(\"TERM\")", "terminal display only; does not shape emitted code" },
    { "progress.cpp", "getenv(\"COLUMNS\")", "terminal display width only; does not shape emitted code" },
    { "progress.cpp", "getenv(\"GOOSE_PROGRESS\")", "progress display mode only; does not shape emitted code" },
    { "format.h", "filesystem::canonical(filesystem::path(path), ec)", "formatter path resolution, outside compilation" },
    { "format.h", "filesystem::status(target, ec)", "formatter preserves permissions, outside compilation" },
    { "format.h", "fopen(tmp.c_str(), \"wb\")", "formatter writes, outside compilation" },
    { "format.h", "filesystem::recursive_directory_iterator", "formatter directory traversal, outside compilation" },
    { "format.h", "filesystem::exists(e.path() / \"CMakeCache.txt\", ec2)", "formatter skips build directories, outside compilation" },
    { "format.h", "fread(buf, 1, sizeof buf, stdin)", "formatter stdin, outside compilation" },
    { "format.h", "filesystem::is_directory(filesystem::path(p), ec)", "formatter argument classification, outside compilation" },
    { "format.h", "filesystem::exists(filesystem::path(p), ec)", "formatter argument existence, outside compilation" },
    { "progress.cpp", "auto v = getenv(name);", "terminal color controls only; does not shape emitted code" },
    { "typecheck_calls.h", "getenv(\"GOOSE_ROUNDS\")", "a trace to stderr" },
};

int main() {
    auto src = fs::path(__FILE__).parent_path() / ".." / "src";
    auto generated = R"test(auto body = R"emit(static void f() { fopen(path, "rb"); })emit";)test";
    auto actual = R"test(FILE *input = fopen(path.c_str(), "rb");)test";
    auto statIdentifier = R"test(void register_stat();)test";
    auto statAfterIdentifier = R"test(register_stat(); stat(path, &info);)test";
    assert(!has_file_access_pattern(code_without_comments_or_literals(generated)));
    assert(has_file_access_pattern(code_without_comments_or_literals(actual)));
    assert(!has_file_access_pattern(code_without_comments_or_literals(statIdentifier)));
    assert(has_file_access_pattern(code_without_comments_or_literals(statAfterIdentifier)));
    auto failures = 0;
    auto files = 0;
    for (auto &e : fs::recursive_directory_iterator(src)) {
        if (!e.is_regular_file()) continue;
        auto ext = e.path().extension().string();
        if (ext != ".h" && ext != ".cpp") continue;
        auto rel = fs::relative(e.path(), src).generic_string();
        if (rel.compare(0, 8, "runtime/") == 0) continue;
        auto skip = false;
        for (auto s : skipped) skip = skip || rel.find(s) != string::npos;
        if (skip) continue;
        files++;
        std::ifstream in(e.path());
        string contents{std::istreambuf_iterator<char>(in), std::istreambuf_iterator<char>()};
        std::istringstream source(contents);
        std::istringstream filtered(code_without_comments_or_literals(contents));
        string line;
        string code;
        for (int n = 1; std::getline(source, line) && std::getline(filtered, code); n++) {
            if (!has_file_access_pattern(code)) continue;
            auto base = fs::path(rel).filename().string();
            auto ok = false;
            for (auto &a : allowed)
                if (base == a.file && line.find(a.text) != string::npos) { a.used++; ok = true; }
            if (!ok) {
                printf("%s:%d: reads a file or path outside the recording reader: %s\n",
                       rel.c_str(), n, line.c_str());
                failures++;
            }
        }
    }
    for (auto &a : allowed)
        if (!a.used) {
            printf("stale allowance %s: %s (%s)\n", a.file, a.text, a.why);
            failures++;
        }
    if (files < 20) {
        printf("only %d sources were searched\n", files);
        failures++;
    }
    assert(failures == 0);
    printf("ok (%d sources)\n", files);
    return 0;
}
