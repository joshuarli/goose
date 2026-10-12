// Goose compiler — what the emission post-pass is asked to do and what it
// found. Included before the code generator, which records the extents of
// its function bodies when either option is on and otherwise does nothing.
#pragma once

namespace goose {

struct EmitOptions {
    // Merge emitted functions whose bodies are equal (--share).
    bool share = false;
    // Name emitted entities from stable keys instead of creation-order
    // counters (--stable-names).
    bool stable_names = false;
    // Keep what the build report's sharing section needs.
    bool explain = false;
    // Write one C file per unit (--emit-units); implies stable names.
    bool units = false;

    bool PostPass() const { return share || stable_names || units; }
    // The consumed assumptions are noted for stable names, and for the
    // report's explanation of why two bodies differ.
    bool NoteAssumptions() const { return stable_names || explain; }
};
inline EmitOptions emit_options;

// A function body as the code generator wrote it into `code`.
struct EmitSeg {
    FnSpec *sp = nullptr;
    bool twin = false;      // The element-run form of the specialization.
    string name;
    size_t begin = 0, end = 0;
};

// The context-dependent facts the optimizing passes used for a body, which
// the code generator cannot see in the specialization alone: the entry
// facts bounds-check elimination took from call sites, and each call
// inlined into it.
struct ConsumedAssumptions {
    unordered_map<const FnSpec *, string> entry;
    unordered_map<const FnSpec *, vector<const FnSpec *>> inlined;
};
inline ConsumedAssumptions consumed_assumptions;

inline void NoteInlinedCallee(const FnSpec *into, const FnSpec *callee) {
    if (into && emit_options.NoteAssumptions()) consumed_assumptions.inlined[into].push_back(callee);
}

// What sharing did, for the report.
struct ShareStats {
    bool ran = false;
    long long functions_before = 0, functions_after = 0;
    long long bytes_before = 0, bytes_after = 0;          // Function bodies.
    long long code_before = 0, code_after = 0;            // The whole code section.
    long long multi_classes = 0;
    // Pairs of classes of one declaration with equal signatures that did not
    // merge, by the first cause found.
    long long distinct_bounds_checks = 0, distinct_inlined = 0, distinct_callee = 0,
              distinct_other = 0;
    // The bytes of the bodies behind each of those counts.
    long long bounds_check_bytes = 0, inlined_bytes = 0, callee_bytes = 0, other_bytes = 0;
    // Time of the post-pass, which the code generation phase includes.
    double wall_seconds = 0, cpu_seconds = 0;
    // Same declaration key and lowering key, different bodies, in the stable
    // naming scheme.
    long long incomplete_lowering_keys = 0;
    bool stable = false;
    unordered_map<const SFunction *, long long> implementations;
};
inline ShareStats share_stats;

// What the units written for a program are, for the report.
struct UnitStats {
    struct Unit {
        string file, module, kind;
        long long bytes = 0, functions = 0;
    };
    bool ran = false;
    vector<Unit> units;
    unordered_map<const SFunction *, set<string>> function_units;
};
inline UnitStats unit_stats;

}  // namespace goose
