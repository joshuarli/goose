// Goose compiler — the probes the build report reads. Each is a pointer test
// when no report was asked for: nothing is timed, counted or allocated, and
// no key is computed. The report itself (report.h) interprets what is
// recorded here.
#pragma once

#include <chrono>
#include <ctime>

namespace goose {

// The process's high-water resident memory in bytes, -1 where the platform
// cannot say. Defined apart (os.cpp) so that the platform headers it needs
// stay out of the compiler's.
long long ReportPeakRssBytes();

// The generated helper functions that serve many bodies: a walker for the
// size of a variable-size value, a verifier for an image, an equality, a
// renderer, and a worker thread's entry.
enum class HelperKind { SizeWalker, ImageVerifier, Equality, Renderer, ThreadEntry, Count };
constexpr int kHelperKinds = (int)HelperKind::Count;

inline const char *HelperKindName(HelperKind k) {
    static const char *names[] = { "size_walker", "image_verifier", "equality", "renderer",
                                   "thread_entry" };
    static_assert(sizeof names / sizeof *names == kHelperKinds);
    return names[(int)k];
}

enum class Phase {
    ParseResolve, CheckSpecialize, Optimize, BoundsCheckElimination, CodeGeneration,
    WriteOutput, NativeBuild, ReportCollection,
    Count
};
constexpr int kPhases = (int)Phase::Count;

inline const char *PhaseName(Phase p) {
    static const char *names[] = { "parse_and_resolve", "check_and_specialize", "optimize",
                                   "bounds_check_elimination", "code_generation",
                                   "write_output", "native_build", "report_collection" };
    static_assert(sizeof names / sizeof *names == kPhases);
    return names[(int)p];
}

struct BuildRecorder {
    static double Wall() {
        return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch())
            .count();
    }
    // CPU time of the whole process, the compile thread included.
    static double Cpu() { return (double)std::clock() / CLOCKS_PER_SEC; }

    // Phases, each a stretch between two Enter calls. Entering a phase again
    // adds to it.
    struct PhaseTotal {
        double wall = 0, cpu = 0;
        long long peak_rss = -1;    // At the end of its latest stretch.
        bool ran = false;
    };
    PhaseTotal phase[kPhases];
    bool running = false;
    Phase current = Phase::ParseResolve;
    double markwall = 0, markcpu = 0, startwall = 0, startcpu = 0, endwall = 0, endcpu = 0;

    void Close() {
        auto w = Wall(), c = Cpu();
        auto &p = phase[(int)current];
        p.wall += w - markwall;
        p.cpu += c - markcpu;
        p.peak_rss = ReportPeakRssBytes();
        p.ran = true;
        markwall = w;
        markcpu = c;
    }
    void Enter(Phase next) {
        if (running) Close();
        else {
            running = true;
            startwall = markwall = Wall();
            startcpu = markcpu = Cpu();
        }
        current = next;
        markwall = Wall();
        markcpu = Cpu();
    }
    void Finish() {
        if (!running) return;
        Close();
        running = false;
        endwall = markwall;
        endcpu = markcpu;
    }

    // What the report's own collection spent its CPU time on, by part, so that
    // its cost can be attributed.
    map<string, double> collection_cpu;

    // Self time of each body check: the time in a check excluding the checks
    // of callees reached for the first time from inside it.
    struct CheckFrame {
        const FnSpec *spec;
        double mark;
        double self;
    };
    vector<CheckFrame> checkstack;
    unordered_map<const FnSpec *, double> selfcheck;

    void CheckEnter(const FnSpec *spec) {
        auto now = Wall();
        if (!checkstack.empty()) {
            auto &parent = checkstack.back();
            parent.self += now - parent.mark;
        }
        checkstack.push_back({ spec, now, 0 });
    }
    void CheckExit(const FnSpec *spec) {
        auto now = Wall();
        auto frame = checkstack.back();
        checkstack.pop_back();
        selfcheck[spec] += frame.self + (now - frame.mark);
        if (!checkstack.empty()) checkstack.back().mark = now;
    }

    // Inlining: each expansion and the callee's size at that moment.
    struct Inlined {
        long long expansions = 0, nodes = 0;
    };
    Inlined inlined;
    unordered_map<const SFunction *, long long> inlined_nodes;   // By callee.

    // Emission: bytes of each body, including element-run twins, and of each
    // kind of helper.
    struct Emitted {
        long long bytes = 0, bodies = 0, twins = 0;
    };
    unordered_map<const SFunction *, Emitted> emitted;
    long long body_bytes = 0, twin_bodies = 0;
    long long helper_count[kHelperKinds] = {}, helper_bytes[kHelperKinds] = {};
};

inline BuildRecorder *build_recorder = nullptr;

// Adds the CPU time of its scope to a named part of the report's collection.
struct CollectionPart {
    const char *name;
    double start = BuildRecorder::Cpu();
    explicit CollectionPart(const char *n) : name(n) {}
    ~CollectionPart() {
        if (build_recorder) build_recorder->collection_cpu[name] += BuildRecorder::Cpu() - start;
    }
};

// Brackets the check of one specialization's body.
struct ReportCheckScope {
    const FnSpec *spec = nullptr;
    explicit ReportCheckScope(const FnSpec *s) {
        if (!build_recorder) return;
        spec = s;
        build_recorder->CheckEnter(s);
    }
    ~ReportCheckScope() {
        if (spec) build_recorder->CheckExit(spec);
    }
    ReportCheckScope(const ReportCheckScope &) = delete;
    ReportCheckScope &operator=(const ReportCheckScope &) = delete;
};

// A call site was inlined; `nodes` is the callee's size as the inliner
// measured it.
inline void ReportInlined(const FnSpec *callee, int nodes) {
    if (!build_recorder) return;
    build_recorder->inlined.expansions++;
    build_recorder->inlined.nodes += nodes;
    build_recorder->inlined_nodes[callee->sf] += nodes;
}

// A specialization's body (or its element-run twin) was written as `bytes`
// bytes of C.
inline void ReportBodyEmitted(const FnSpec *sp, bool twin, size_t bytes) {
    if (!build_recorder) return;
    auto &e = build_recorder->emitted[sp->sf];
    e.bytes += (long long)bytes;
    e.bodies++;
    e.twins += twin;
    build_recorder->body_bytes += (long long)bytes;
    build_recorder->twin_bodies += twin;
}

inline void ReportHelperEmitted(HelperKind kind, size_t bytes) {
    if (!build_recorder) return;
    build_recorder->helper_count[(int)kind]++;
    build_recorder->helper_bytes[(int)kind] += (long long)bytes;
}

}  // namespace goose
