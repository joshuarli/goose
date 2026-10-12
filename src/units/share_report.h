// Goose compiler — the build report's sharing section.
#pragma once

namespace goose {

inline void ReportSharingJson(JsonOut &j) {
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
    j.F("incomplete_lowering_keys", s.incomplete_lowering_keys);
    j.EndObj();
}

}  // namespace goose
