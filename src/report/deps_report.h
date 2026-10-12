// Goose compiler — the dependency section of the build report
// (`extensions.dependencies`). For every checked context, and every global
// initializer, it lists what the check consulted as (kind, subject, digest)
// triples, and digests of what the check produced, so that two reports of a
// program before and after an edit can be compared without recompiling
// anything (test/scale/predict.py).
#pragma once

#include "report.h"
#include "../ident/deps.h"

namespace goose {

constexpr const char *kDependenciesFormat = "goose-dependencies/1";

// The files a compile read, named relative to the program's own directory
// where they lie under it, so that the same program checked out elsewhere
// reports the same names.
inline string DepsInputName(const string &path, const string &root) {
    auto slash = root.find_last_of("/\\");
    auto dir = slash == string::npos ? string() : root.substr(0, slash + 1);
    if (!dir.empty() && path.compare(0, dir.size(), dir) == 0) return path.substr(dir.size());
    return path;
}

inline void DepsWrite(JsonOut &j) {
    j.Key("dependencies");
    if (!g_deps) {
        j.Null();
        return;
    }
    auto &rec = *g_deps;
    auto &root = g_build_report->input;
    j.Obj();
    j.F("format", kDependenciesFormat);
    j.Key("inputs").Obj();
    j.Key("files_read").Arr();
    {
        vector<pair<string, Digest>> files;
        for (auto &[path, d] : rec.filesread) files.push_back({ DepsInputName(path, root), d });
        sort(files.begin(), files.end());
        for (auto &[path, d] : files) j.Obj().F("path", path).F("digest", d.Stored()).EndObj();
    }
    j.EndArr();
    j.Key("paths_absent").Arr();
    {
        vector<string> absent;
        for (auto &path : rec.pathsabsent) absent.push_back(DepsInputName(path, root));
        sort(absent.begin(), absent.end());
        for (auto &path : absent) j.Str(path);
    }
    j.EndArr();
    j.EndObj();

    // Contexts that the key does not tell apart are reported as one, with
    // every digest of each: a prediction then holds for the group.
    vector<size_t> order(rec.contexts.size());
    for (size_t i = 0; i < order.size(); i++) order[i] = i;
    sort(order.begin(), order.end(), [&](size_t a, size_t b) {
        return rec.contexts[a].key < rec.contexts[b].key;
    });
    j.Key("contexts").Arr();
    for (size_t i = 0; i < order.size();) {
        size_t end = i;
        while (end < order.size() && rec.contexts[order[end]].key == rec.contexts[order[i]].key) end++;
        auto &first = rec.contexts[order[i]];
        vector<Digest> results, positions, callers;
        vector<DepEntry> deps;
        for (auto k = i; k < end; k++) {
            auto &c = rec.contexts[order[k]];
            results.push_back(c.result);
            positions.push_back(c.positions);
            callers.push_back(c.callers);
            for (auto &d : c.deps) deps.push_back(d);
        }
        auto combine = [](vector<Digest> &v) {
            sort(v.begin(), v.end());
            if (v.size() == 1) return v[0];
            Canon c;
            for (auto &d : v) c.Dig(d);
            return c.Hash();
        };
        sort(deps.begin(), deps.end(), [](const DepEntry &a, const DepEntry &b) {
            if (a.kind != b.kind) return a.kind < b.kind;
            if (a.subject != b.subject) return a.subject < b.subject;
            return a.digest < b.digest;
        });
        deps.erase(unique(deps.begin(), deps.end(), [](const DepEntry &a, const DepEntry &b) {
                       return a.kind == b.kind && a.subject == b.subject && a.digest == b.digest;
                   }),
                   deps.end());
        j.Obj();
        j.F("key", first.key.Stored()).F("decl", first.decl.Stored());
        j.F("name", first.sf ? ReportFunctionName(first.sf) : first.name);
        j.F("kind", first.global ? "global" : "function");
        j.F("duplicates", (long long)(end - i));
        j.F("result", combine(results).Stored());
        j.F("positions", combine(positions).Stored());
        j.F("callers", combine(callers).Stored());
        j.Key("dependencies").Arr();
        for (auto &d : deps)
            j.Obj().F("kind", DepKindName(d.kind)).F("subject", d.subject)
                .F("digest", d.digest.Stored()).EndObj();
        j.EndArr();
        j.EndObj();
        i = end;
    }
    j.EndArr();
    j.EndObj();
}

}  // namespace goose
