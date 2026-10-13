// The compile's input recording (units/build.h) is complete only if the
// frontend reads files, and asks about paths, through the four functions that
// tell the recorder: LoadFile, PathExists, FileExists and ProbeDirectory. This
// reads the compiler's sources and fails on any other way of reading a file
// or asking about a path, unless the use is listed below with its reason.
//
// What it covers: every header and source of src/ except the files named in
// `skipped`, searched for the C and C++ standard library calls that open, read
// or stat a file or list a directory, and for getenv. What it cannot see: a
// read made some other way (open(2), mmap, popen, a platform call), a read by
// a process the compiler starts (the C compiler, cmake, git), reads inside
// third_party/, a file read through one of the four functions by a caller that
// should not have (they record whatever they are given), and the process's
// working directory and clock, which the build records or ignores by other
// means. Keep assertions active even in an optimized test build.
#ifdef NDEBUG
#undef NDEBUG
#endif
#include <algorithm>
#include <cassert>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

namespace fs = std::filesystem;
using std::string;
using std::vector;

struct Allowed {
    const char *file;
    const char *text;       // A substring of the line.
    const char *why;
    int used = 0;
};

// Files that are not the compile: the build step that runs after it, tool
// discovery, the linter's own path, and generated or emitted text.
static const char *skipped[] = {
    "build.h",          // The build step after the compile.
    "toolchain.h",      // Finds the C compiler; defines PathExists.
    "jit.h",            // Runs the program.
    "runtime_inline.h", // Generated.
    "lint_facts.h",     // The linter, which is not a build.
    "units/build.h",    // The build step, and the recorder's own reads.
    "process.cpp",      // Runs and finds programs; the programs are not inputs.
    "core/",            // Emits Core files.
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
    { "main.cpp", "fopen(headername.c_str(), \"wb\")", "writes" },
    { "report.h", "fopen(r.path.c_str(), \"wb\")", "writes" },
    { "emit.h", "fopen(path.c_str(), \"wb\")", "writes the units" },
    { "main.cpp", "filesystem::directory_iterator(", "a --verify-reuse hit comparing the store's own units" },
    { "main.cpp", "getenv(\"GOOSE_STDLIB\")", "named in the contract" },
    { "main.cpp", "getenv(\"GOOSE_RUNTIME\")", "named in the contract; the runtime's source search" },
    { "native.h", "recursive_directory_iterator", "the native build's inputs, which a build with such a part does not skip" },
    { "native.h", "directory_iterator(filesystem::path(replydir)", "the native build's cmake reply" },
    { "native.h", "last_write_time", "the native build's freshness" },
    { "packages.h", "filesystem::exists(p, ec)", "removing a cached checkout" },
    { "packages.h", "recursive_directory_iterator(p, ec)", "removing a cached checkout" },
    { "typecheck_calls.h", "getenv(\"GOOSE_ROUNDS\")", "a trace to stderr" },
};

static bool word_before(const string &line, size_t at) {
    if (at == 0) return false;
    auto c = line[at - 1];
    return isalnum((unsigned char)c) || c == '_';
}

int main() {
    auto src = fs::path(__FILE__).parent_path() / ".." / "src";
    vector<string> patterns = { "fopen(", "ifstream", "fstream", "filesystem::exists",
        "filesystem::is_directory", "filesystem::is_regular_file", "directory_iterator",
        "filesystem::file_size", "filesystem::last_write_time", "filesystem::status",
        "filesystem::canonical", "opendir", "readdir", "fread(", "getenv(", "stat(", "access(" };
    auto failures = 0;
    auto files = 0;
    for (auto &e : fs::recursive_directory_iterator(src)) {
        if (!e.is_regular_file()) continue;
        auto ext = e.path().extension().string();
        if (ext != ".h" && ext != ".cpp") continue;
        auto rel = fs::relative(e.path(), src).generic_string();
        if (rel.compare(0, 8, "runtime/") == 0) continue;     // C the compiler writes out.
        auto skip = false;
        for (auto s : skipped) skip = skip || rel.find(s) != string::npos;
        if (skip) continue;
        files++;
        std::ifstream in(e.path());
        string line;
        for (int n = 1; std::getline(in, line); n++) {
            auto comment = line.find("//");
            auto code = comment == string::npos ? line : line.substr(0, comment);
            for (auto &p : patterns) {
                auto at = code.find(p);
                if (at == string::npos) continue;
                // `stat(` and `access(` as whole words only.
                if ((p == "stat(" || p == "access(") && word_before(code, at)) continue;
                auto base = fs::path(rel).filename().string();
                auto ok = false;
                for (auto &a : allowed)
                    if (base == a.file && line.find(a.text) != string::npos) { a.used++; ok = true; }
                if (!ok) {
                    printf("%s:%d: reads a file or path outside the recording reader: %s\n",
                           rel.c_str(), n, line.c_str());
                    failures++;
                }
                break;
            }
        }
    }
    // An entry that matches nothing is a use that went away, or a typo.
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
