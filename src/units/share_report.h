// Goose compiler — the build report's sharing section.
#pragma once

namespace goose {

inline void ReportSharingJson(BuildReportJson &j) {
    auto &s = share_stats;
    if (!emit_options.share || !s.ran) {
        j.Null();
        return;
    }
    j.Obj();
    j.F("stable_names", s.stable);
    j.F("functions_before", s.functions_before).F("functions_after", s.functions_after);
    j.F("classes_with_several_members", s.multi_classes);
    j.F("function_bytes_before", s.bytes_before).F("function_bytes_after", s.bytes_after);
    j.F("code_section_bytes_before", s.code_before).F("code_section_bytes_after", s.code_after);
    // Implementations of one declaration, with equal signatures, that stayed
    // apart: the first cause found when each is compared with the
    // declaration's first.
    j.Key("not_merged_same_declaration").Obj()
        .F("bounds_check_sites", s.distinct_bounds_checks)
        .F("inlined_calls", s.distinct_inlined)
        .F("callee", s.distinct_callee)
        .F("other", s.distinct_other).EndObj();
    // The bytes of the bodies that stayed apart for each cause.
    j.Key("not_merged_same_declaration_bytes").Obj()
        .F("bounds_check_sites", s.bounds_check_bytes)
        .F("inlined_calls", s.inlined_bytes)
        .F("callee", s.callee_bytes)
        .F("other", s.other_bytes).EndObj();
    // The post-pass's own time, which code_generation includes.
    j.Key("phase_seconds").Obj().F("wall", s.wall_seconds).F("cpu", s.cpu_seconds).EndObj();
    j.F("incomplete_lowering_keys", s.incomplete_lowering_keys);
    j.EndObj();
}

// The units written for the program: how many, how big, and what each holds,
// so that a changed unit can be attributed to the functions in it.
inline void ReportUnitsJson(BuildReportJson &j) {
    auto &s = unit_stats;
    if (!s.ran) {
        j.Null();
        return;
    }
    vector<long long> sizes;
    for (auto &u : s.units) sizes.push_back(u.bytes);
    sort(sizes.begin(), sizes.end());
    j.Obj().F("count", (long long)s.units.size());
    j.Key("bytes").Obj();
    j.F("min", sizes.front()).F("median", sizes[sizes.size() / 2]).F("max", sizes.back());
    j.EndObj();
    // Where the bytes go: per unit, and in total with the runtime header every
    // unit includes counted once. `location_externs` is part of `externs` and
    // `location_references` part of `functions`.
    auto parts = [&](const UnitStats::Breakdown &p) {
        j.Obj().F("header", p.header).F("types", p.types).F("layouts", p.layouts)
            .F("includes", p.includes).F("externs", p.externs)
            .F("location_externs", p.location_externs).F("definitions", p.definitions)
            .F("functions", p.functions).F("location_references", p.location_references).EndObj();
    };
    UnitStats::Breakdown total;
    for (auto &u : s.units) {
        total.header += u.parts.header; total.types += u.parts.types; total.layouts += u.parts.layouts;
        total.includes += u.parts.includes; total.externs += u.parts.externs;
        total.location_externs += u.parts.location_externs; total.definitions += u.parts.definitions;
        total.functions += u.parts.functions; total.location_references += u.parts.location_references;
    }
    j.Key("breakdown").Obj().F("runtime_header_bytes", s.runtime_header_bytes);
    j.Key("total");
    parts(total);
    j.EndObj();
    j.Key("units").Arr();
    for (auto &u : s.units) {
        j.Obj().F("file", u.file).F("module", u.module).F("kind", u.kind).F("bytes", u.bytes)
            .F("functions", u.functions);
        j.Key("parts");
        parts(u.parts);
        j.EndObj();
    }
    j.EndArr();
    j.EndObj();
}

}  // namespace goose
