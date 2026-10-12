// Goose compiler — the build report (`--build-report FILE`). It says where a
// program's build cost comes from: how many contexts the checker made and how
// many of them survive, what each source function costs in bytes and time,
// which specialization dimensions multiply its contexts, and how long each
// phase took. It observes the compile and changes nothing in it: every probe
// is inert without the flag, and the lint verb never reaches this code.
#pragma once

#include "hooks.h"
#include "../ident/keys.h"

namespace goose {

string RuntimeVersion();

constexpr const char *kBuildReportFormat = "goose-build-report/1";

// A JSON writer small enough to need nothing else. A comma is due before a
// value or key whenever the enclosing container already holds one.
class JsonOut {
    string out;
    vector<bool> due;

    void Sep() {
        if (due.empty()) return;
        if (due.back()) out += ',';
        due.back() = true;
    }
    void Quoted(string_view s) {
        out += '"';
        for (auto c : s) {
            auto u = (uint8_t)c;
            if (c == '"' || c == '\\') { out += '\\'; out += c; }
            else if (u == '\n') out += "\\n";
            else if (u == '\t') out += "\\t";
            else if (u < 32) { char buf[8]; snprintf(buf, sizeof buf, "\\u%04x", u); out += buf; }
            else out += c;
        }
        out += '"';
    }

public:
    JsonOut &Obj() { Sep(); out += '{'; due.push_back(false); return *this; }
    JsonOut &Arr() { Sep(); out += '['; due.push_back(false); return *this; }
    JsonOut &EndObj() { due.pop_back(); out += '}'; return *this; }
    JsonOut &EndArr() { due.pop_back(); out += ']'; return *this; }
    JsonOut &Key(string_view k) {
        Sep();
        Quoted(k);
        out += ':';
        due.back() = false;
        return *this;
    }
    JsonOut &Str(string_view s) { Sep(); Quoted(s); return *this; }
    JsonOut &Int(long long v) { Sep(); out += to_string(v); return *this; }
    JsonOut &Num(double v) {
        Sep();
        char buf[48];
        snprintf(buf, sizeof buf, "%.6f", v);
        out += buf;
        return *this;
    }
    JsonOut &Bool(bool v) { Sep(); out += v ? "true" : "false"; return *this; }
    JsonOut &Null() { Sep(); out += "null"; return *this; }
    // A nullable measurement: -1 is "not available here".
    JsonOut &OptInt(long long v) { return v < 0 ? Null() : Int(v); }
    JsonOut &F(string_view k, string_view v) { return Key(k).Str(v); }
    JsonOut &F(string_view k, long long v) { return Key(k).Int(v); }
    JsonOut &F(string_view k, int v) { return Key(k).Int(v); }
    JsonOut &F(string_view k, size_t v) { return Key(k).Int((long long)v); }
    JsonOut &F(string_view k, double v) { return Key(k).Num(v); }
    JsonOut &F(string_view k, bool v) { return Key(k).Bool(v); }
    JsonOut &F(string_view k, const char *v) { return Key(k).Str(v); }
    const string &Text() const { return out; }
};

// Why the checker made a second specialization whose key equals an earlier
// one's, as far as the specialization's own flags say.
enum class DuplicateReason { StoresOutside, RecursiveCycle, FunctionValue, Unclassified, Count };
inline const char *DuplicateReasonName(DuplicateReason r) {
    static const char *names[] = { "stores_outside_activation", "recursive_cycle",
                                   "function_value_environment", "unclassified" };
    return names[(int)r];
}

// What the report knows about one source function.
struct FunctionFacts {
    const SFunction *sf = nullptr;
    Digest decl;
    string name, module;
    vector<const FnSpec *> specs;
    long long nodes_before = 0, nodes_after = 0, live = 0;
    Digest contexts_key;
    long long duplicates = 0;
    struct DimStat {
        long long distinct = 0, merged = 0;
    };
    DimStat dims[kSpecDims];
};

struct BuildReport {
    BuildRecorder rec;
    string path;
    string input;
    int optlevel = 0;
    // `--check` runs the frontend and reports it only: no fact that needs
    // the optimizer's or the code generator's results is computed.
    bool frontend_only = false;
    unique_ptr<KeyMaker> keys;
    vector<FunctionFacts> functions;

    long long source_functions = 0, checked_contexts = 0, entry_reachable = 0;
    long long duplicate_contexts = 0;
    long long duplicate_reasons[(int)DuplicateReason::Count] = {};
    long long live_instances = -1;
    long long twin_instances = 0, thread_entries = 0, body_instances = 0;
    bool emitted = false;

    struct Section {
        long long count = 0, bytes = 0;
    };
    // Set once the C file has been written.
    bool wrote = false;
    string out_path;
    long long out_bytes = 0;
    Section runtime, types, literals, globals, protos, bodies, glue;
    long long extern_support_bytes = 0, predef_bytes = 0;
};

inline unique_ptr<BuildReport> g_build_report;

inline long long ReportCountNodes(Node *root) {
    if (!root) return 0;
    unordered_set<const Node *> seen;
    long long n = 0;
    function<void(Node *)> walk = [&](Node *node) {
        if (!node || !seen.insert(node).second) return;
        n++;
        node->Children([&](Node *c) { walk(c); });
    };
    walk(root);
    return n;
}

// The readable name of a function: `ns::name(param types)`, nested functions
// under the function that holds them.
inline string ReportFunctionName(const SFunction *sf) {
    string s;
    if (sf->isnested && sf->outer) s = ReportFunctionName(sf->outer) + "/";
    s += sf->qname;
    s += "(";
    for (size_t i = 0; i < sf->params.size(); i++) {
        if (i) s += ", ";
        if (sf->params[i].type) sf->params[i].type->Dump(s, 400);
        else s += "_";
    }
    return s + ")";
}

// The contexts reachable from the entry points before optimization: the
// population the linter's `specialization_fanout` counts. This is a read-only
// copy of the walk the lint facts make, so that neither depends on the other.
inline long long ReportEntryReachable(Ast &ast) {
    unordered_set<const FnSpec *> reachable, scanned;
    vector<const FnSpec *> pending;
    auto enqueue = [&](const FnSpec *spec) {
        if (spec && reachable.insert(spec).second) pending.push_back(spec);
    };
    if (auto mainsf = ast.MainFunction())
        for (auto spec : mainsf->specs) enqueue(spec);
    auto scan = [&](Node *root) {
        unordered_set<const Node *> seen;
        function<void(Node *)> walk = [&](Node *node) {
            if (!node || !seen.insert(node).second) return;
            if (auto call = Is<Call>(node)) {
                enqueue(call->spec);
                for (auto spec : call->dispatch) enqueue(spec);
                for (auto &[type, spec] : call->fmtspecs) enqueue(spec);
                if (call->builtin == B_THREAD_SPAWN && !call->args.empty()) {
                    if (auto ident = Is<Ident>(call->args[0]); ident && ident->fnref)
                        for (auto spec : ident->fnref->specs) enqueue(spec);
                }
                for (auto arg : call->args) walk(arg);
                walk(call->callee);
                if (call->fvbody) walk(call->fvbody);
                return;
            }
            if (Is<FunVal>(node) || Is<FnDecl>(node)) return;
            node->Children([&](Node *child) { walk(child); });
        };
        walk(root);
    };
    for (auto global : ast.globals) scan(global);
    for (size_t next = 0; next < pending.size(); next++) {
        auto spec = pending[next];
        if (!scanned.insert(spec).second) continue;
        scan(spec->body);
    }
    return (long long)reachable.size();
}

inline void BuildReportStart(const string &path, const string &input, int optlevel,
                             bool frontend_only) {
    g_build_report = make_unique<BuildReport>();
    g_build_report->path = path;
    g_build_report->input = input;
    g_build_report->optlevel = optlevel;
    g_build_report->frontend_only = frontend_only;
    build_recorder = &g_build_report->rec;
    g_build_report->rec.Enter(Phase::ParseResolve);
}

inline void BuildReportPhase(Phase p) {
    if (g_build_report) g_build_report->rec.Enter(p);
}

// The checked program, before the optimizer touches it: counts, keys, and
// the per-function and per-dimension attribution of its contexts.
inline void BuildReportAfterCheck(Ast &ast) {
    auto &r = *g_build_report;
    r.rec.Enter(Phase::ReportCollection);
    r.keys = make_unique<KeyMaker>(ast);
    auto &keys = *r.keys;
    r.source_functions = (long long)ast.functions.size();
    r.checked_contexts = (long long)ast.fnspecs.size();
    r.entry_reachable = ReportEntryReachable(ast);

    unordered_map<const SFunction *, size_t> index;
    for (auto sf : ast.functions) {
        index[sf] = r.functions.size();
        FunctionFacts f;
        f.sf = sf;
        f.decl = keys.Decl(sf).digest;
        f.name = ReportFunctionName(sf);
        f.module = keys.ModuleOf(sf->line.fileidx);
        r.functions.push_back(std::move(f));
    }
    for (auto spec : ast.fnspecs) {
        if (!spec->sf) continue;
        auto it = index.find(spec->sf);
        if (it == index.end()) continue;
        auto &f = r.functions[it->second];
        f.specs.push_back(spec);
        f.nodes_before += ReportCountNodes(spec->body);
    }
    for (auto &f : r.functions) {
        // Contexts with equal keys are duplicates: the checker made a second
        // specialization where the reuse test could not take the first (a
        // body that stored into its caller's variables, say, or a member of
        // a recursive cycle). They are counted apart and left out of the
        // dimension counts, which are about contexts that differ.
        vector<const ContextKey *> ctx;
        unordered_map<Digest, const FnSpec *, DigestHash> first;
        vector<Digest> totals;
        for (auto spec : f.specs) {
            auto &key = keys.Context(spec);
            totals.push_back(key.total);
            auto [it, fresh] = first.emplace(key.total, spec);
            if (fresh) {
                ctx.push_back(&key);
                continue;
            }
            f.duplicates++;
            auto prior = it->second;
            auto reason = prior->storesout || spec->storesout ? DuplicateReason::StoresOutside
                          : prior->incycle || spec->incycle    ? DuplicateReason::RecursiveCycle
                          : prior->isfunval || spec->isfunval  ? DuplicateReason::FunctionValue
                                                               : DuplicateReason::Unclassified;
            r.duplicate_reasons[(int)reason]++;
        }
        r.duplicate_contexts += f.duplicates;
        sort(totals.begin(), totals.end());
        Canon set;
        set.Tag('K').U(totals.size());
        for (auto &t : totals) set.Dig(t);
        f.contexts_key = set.Hash();
        // Per dimension: how many values the function's distinct contexts
        // take, and by how many contexts the function would shrink if that
        // dimension alone were ignored (contexts minus the groups that agree
        // on all the others). A dimension with one value merges nothing.
        for (int d = 0; d < kSpecDims; d++) {
            unordered_set<Digest, DigestHash> values, groups;
            for (auto c : ctx) values.insert(c->dims[d]);
            f.dims[d].distinct = (long long)values.size();
            if (values.size() < 2) continue;
            for (auto c : ctx) {
                Canon rest;
                for (int j = 0; j < kSpecDims; j++)
                    if (j != d) rest.Dig(c->dims[j]);
                groups.insert(rest.Hash());
            }
            f.dims[d].merged = (long long)(ctx.size() - groups.size());
        }
    }
    r.rec.Enter(Phase::Optimize);
}

// The optimized program: what survived reachability and how big it is now.
inline void BuildReportAfterOptimize(Ast &ast) {
    auto &r = *g_build_report;
    r.rec.Enter(Phase::ReportCollection);
    unordered_map<const SFunction *, size_t> index;
    for (size_t i = 0; i < r.functions.size(); i++) index[r.functions[i].sf] = i;
    r.live_instances = 0;
    for (auto spec : ast.fnspecs) {
        if (!spec->live || !spec->body) continue;
        r.live_instances++;
        auto it = index.find(spec->sf);
        if (it == index.end()) continue;
        r.functions[it->second].live++;
        r.functions[it->second].nodes_after += ReportCountNodes(spec->body);
    }
}

inline void BuildReportAfterCodegen(CodeGen &cg) {
    auto &r = *g_build_report;
    r.rec.Enter(Phase::ReportCollection);
    r.emitted = true;
    r.body_instances = (long long)cg.livespecs.size();
    r.twin_instances = (long long)cg.erqueue.size();
    r.thread_entries = (long long)cg.thunks.size();
}

// A declaration is introduced by a leading token; counting those counts the
// declarations of a generated section without parsing it.
inline long long ReportCountOf(const string &text, string_view token) {
    long long n = 0;
    for (auto pos = text.find(token); pos != string::npos; pos = text.find(token, pos + token.size()))
        n++;
    return n;
}

// The finished C file: how its bytes divide among what the report names.
// `runtime_bytes` and `runtime_sections` are the runtime text pasted around
// the generated program.
inline void BuildReportOutput(CodeGen &cg, const string &file, size_t bytes, size_t runtime_bytes,
                              int runtime_sections) {
    auto &r = *g_build_report;
    r.rec.Enter(Phase::ReportCollection);
    r.wrote = true;
    r.out_path = file;
    r.out_bytes = (long long)bytes;
    r.runtime = { runtime_sections, (long long)runtime_bytes };
    r.types = { ReportCountOf(cg.tdecls, "typedef "), (long long)cg.tdecls.size() };
    r.literals = { ReportCountOf(cg.pdata, "static const "), (long long)cg.pdata.size() };
    r.globals = { ReportCountOf(cg.data, "static "), (long long)cg.data.size() };
    r.protos = { ReportCountOf(cg.protos, "\n"), (long long)cg.protos.size() };
    r.extern_support_bytes = (long long)(cg.result.size() - cg.code.size() - cg.protos.size());
    r.predef_bytes = (long long)cg.predefs.size();
    auto &rec = r.rec;
    long long helper_bytes = 0;
    for (int k = 0; k < kHelperKinds; k++) helper_bytes += rec.helper_bytes[k];
    r.bodies = { r.body_instances + r.twin_instances, rec.body_bytes };
    // Everything else in the code section: the global initializer, program
    // start, exports and main.
    r.glue = { 0, (long long)cg.code.size() - rec.body_bytes - helper_bytes };
}

inline void ReportPhaseJson(JsonOut &j, const BuildRecorder::PhaseTotal &p) {
    j.Obj().F("wall_seconds", p.wall).F("cpu_seconds", p.cpu);
    j.Key("peak_rss_bytes").OptInt(p.peak_rss);
    j.EndObj();
}

// Writes the report. The compile has finished; `filename` is the program.
inline void BuildReportWrite() {
    auto &r = *g_build_report;
    r.rec.Finish();
    auto &rec = r.rec;
    JsonOut j;
    j.Obj();
    j.F("format", kBuildReportFormat);
    j.F("runtime_version", RuntimeVersion());
    j.Key("input").Obj().F("file", r.input).F("optimization_level", r.optlevel)
        .F("mode", r.frontend_only ? "check" : "emit").EndObj();

    // Counts.
    j.Key("counts").Obj();
    j.F("source_functions", r.source_functions);
    j.F("checked_contexts", r.checked_contexts);
    j.F("entry_reachable_contexts", r.entry_reachable);
    j.Key("duplicate_contexts").Obj().F("count", r.duplicate_contexts);
    for (int i = 0; i < (int)DuplicateReason::Count; i++)
        j.F(DuplicateReasonName((DuplicateReason)i), r.duplicate_reasons[i]);
    j.EndObj();
    j.Key("live_instances").OptInt(r.live_instances);
    j.Key("emitted_instances");
    if (!r.emitted) j.Null();
    else {
        j.Obj().F("total", r.body_instances + r.twin_instances + r.thread_entries)
            .F("bodies", r.body_instances).F("element_run_twins", r.twin_instances)
            .F("thread_entries", r.thread_entries).EndObj();
    }
    j.Key("inline_expansions");
    if (r.live_instances < 0) j.Null();
    else j.Obj().F("call_sites", rec.inlined.expansions).F("nodes_copied", rec.inlined.nodes).EndObj();
    j.Key("generated_helpers");
    if (!r.wrote) j.Null();
    else {
        j.Obj();
        for (int k = 0; k < kHelperKinds; k++)
            j.Key(HelperKindName((HelperKind)k)).Obj().F("count", rec.helper_count[k])
                .F("bytes", rec.helper_bytes[k]).EndObj();
        j.EndObj();
    }
    auto section = [&](const char *name, const BuildReport::Section &s) {
        j.Key(name);
        if (!r.wrote) j.Null();
        else j.Obj().F("count", s.count).F("bytes", s.bytes).EndObj();
    };
    section("type_declarations", r.types);
    section("literal_data", r.literals);
    section("runtime_text", r.runtime);
    j.EndObj();

    // The C file, divided among what is named above. Whatever is not named is
    // `unattributed_bytes`: the file's header comment, build defines and
    // section banners.
    j.Key("output");
    if (!r.wrote) j.Null();
    else {
        long long helpers = 0;
        for (int k = 0; k < kHelperKinds; k++) helpers += rec.helper_bytes[k];
        auto attributed = r.runtime.bytes + r.types.bytes + r.literals.bytes + r.globals.bytes +
                          r.protos.bytes + r.extern_support_bytes + r.predef_bytes +
                          r.bodies.bytes + helpers + r.glue.bytes;
        j.Obj().F("path", r.out_path).F("c_bytes", r.out_bytes);
        j.Key("attributed").Obj();
        j.F("function_bodies", r.bodies.bytes);
        j.F("generated_helpers", helpers);
        j.F("type_declarations", r.types.bytes);
        j.F("literal_data", r.literals.bytes);
        j.F("global_data", r.globals.bytes);
        j.F("prototypes", r.protos.bytes);
        j.F("extern_support", r.extern_support_bytes);
        j.F("program_glue", r.glue.bytes);
        j.F("compiler_defines", r.predef_bytes);
        j.F("runtime_text", r.runtime.bytes);
        j.EndObj();
        j.F("unattributed_bytes", r.out_bytes - attributed);
        j.EndObj();
    }

    // Per source function, in key order.
    vector<size_t> order(r.functions.size());
    for (size_t i = 0; i < order.size(); i++) order[i] = i;
    sort(order.begin(), order.end(), [&](size_t a, size_t b) {
        return r.functions[a].decl < r.functions[b].decl;
    });
    j.Key("functions").Arr();
    for (auto i : order) {
        auto &f = r.functions[i];
        double self = 0;
        for (auto spec : f.specs) {
            auto it = rec.selfcheck.find(spec);
            if (it != rec.selfcheck.end()) self += it->second;
        }
        j.Obj();
        j.F("decl_key", f.decl.Stored()).F("name", f.name).F("module", f.module);
        j.F("contexts", f.specs.size()).F("duplicate_contexts", f.duplicates);
        j.F("contexts_key", f.contexts_key.Stored());
        j.F("self_check_seconds", self);
        j.F("nodes_before_optimization", f.nodes_before);
        if (r.live_instances >= 0) {
            j.F("live_instances", f.live).F("nodes_after_optimization", f.nodes_after);
            auto it = rec.inlined_nodes.find(f.sf);
            j.F("nodes_inlined_elsewhere", it == rec.inlined_nodes.end() ? 0LL : it->second);
        }
        if (r.wrote) {
            auto it = rec.emitted.find(f.sf);
            j.F("emitted_instances", it == rec.emitted.end() ? 0LL : it->second.bodies);
            j.F("emitted_bytes", it == rec.emitted.end() ? 0LL : it->second.bytes);
        }
        // Dimensions along which the function's contexts differ; one that
        // takes a single value is left out.
        j.Key("dimensions").Arr();
        for (int d = 0; d < kSpecDims; d++) {
            if (f.dims[d].distinct < 2) continue;
            j.Obj().F("dimension", SpecDimName((SpecDim)d)).F("distinct_values", f.dims[d].distinct)
                .F("contexts_merged_if_ignored", f.dims[d].merged).EndObj();
        }
        j.EndArr();
        j.EndObj();
    }
    j.EndArr();

    // Per dimension over the whole program: the sums of the per-function
    // numbers, so a dimension is ranked by what it costs overall.
    j.Key("dimensions").Arr();
    for (int d = 0; d < kSpecDims; d++) {
        long long distinct = 0, merged = 0;
        for (auto &f : r.functions) {
            distinct += f.dims[d].distinct;
            merged += f.dims[d].merged;
        }
        j.Obj().F("dimension", SpecDimName((SpecDim)d)).F("distinct_values", distinct)
            .F("contexts_merged_if_ignored", merged).EndObj();
    }
    j.EndArr();

    // Phases. A `--check` run also optimizes and eliminates checks, which the
    // report does not itemize: that time is the remainder.
    j.Key("phases").Obj();
    double wall = 0, cpu = 0;
    for (int p = 0; p < kPhases; p++) {
        auto &t = rec.phase[p];
        if (!t.ran) continue;
        auto ph = (Phase)p;
        if (r.frontend_only && (ph == Phase::Optimize || ph == Phase::BoundsCheckElimination ||
                                ph == Phase::CodeGeneration || ph == Phase::WriteOutput))
            continue;
        j.Key(PhaseName(ph));
        ReportPhaseJson(j, t);
        wall += t.wall;
        cpu += t.cpu;
    }
    j.EndObj();
    long long peak = -1;
    for (auto &t : rec.phase) peak = max(peak, t.peak_rss);
    j.Key("total").Obj();
    j.F("wall_seconds", rec.endwall - rec.startwall).F("cpu_seconds", rec.endcpu - rec.startcpu);
    j.Key("peak_rss_bytes").OptInt(peak);
    j.EndObj();
    j.Key("unattributed_seconds").Obj()
        .F("wall", rec.endwall - rec.startwall - wall).F("cpu", rec.endcpu - rec.startcpu - cpu)
        .EndObj();

    // Reserved for the sections later work adds.
    j.Key("extensions").Obj();
    j.Key("sharing").Null().Key("units").Null().Key("native_compile").Null();
    j.EndObj();
    j.EndObj();

    auto f = fopen(r.path.c_str(), "wb");
    if (!f) throw CompileError { cat("cannot write build report: ", r.path) };
    fwrite(j.Text().data(), 1, j.Text().size(), f);
    fputc('\n', f);
    fclose(f);
}

}  // namespace goose
