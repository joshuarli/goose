// The bundled linter consumes only compiler facts and never opens target code.
import os;
import json;

let MAX_FACTS = 67108864;
let MAX_RECORD = 16777216;
let MAX_RECORDS = 1000000;
let MAX_OUTPUT = 268435456;

struct SourceFact { path: const u8[:], id: i64, byte_length: i64 }
struct WarningFact {
    code: const u8[:], message: const u8[:], file_id: i64,
    line: i64, start_line: i64, start_column: i64,
    end_line: i64, end_column: i64, start_byte: i64, end_byte: i64,
    precision: const u8[:], specialization_json: const u8[:]
}
struct StatementFact { file_id: i64, start_byte: i64, end_byte: i64, start_line: i64, end_line: i64, source_order: i64 }
struct CommentFact { id: i64, file_id: i64, path: const u8[:], start_byte: i64, end_byte: i64, line: i64, form: const u8[:], text: const u8[:] }
struct CoverageFact { file_id: i64, path: const u8[:], checked: i64, unchecked: i64, unsupported_start: i64, unsupported_count: i64 }
struct Facts { revision: const u8[:], profile: const u8[:] }
struct DirectiveState { valid: bool, code: const u8[:], reason: const u8[:], message: const u8[:], statement_index: i64 }
struct OutputDiagnostic {
    code: const u8[:], message: const u8[:], file_id: i64, group: const u8[:], severity: const u8[:], confidence: const u8[:],
    start_byte: i64, end_byte: i64, start_line: i64, start_column: i64,
    end_line: i64, end_column: i64, precision: const u8[:],
    suppressed: bool, suppression_reason: const u8[:],
    suppression_file_id: i64, suppression_start: i64, suppression_end: i64, suppression_line: i64,
    evidence_json: const u8[:], specialization_json: const u8[:],
    baseline_fingerprint: const u8[:], baseline_occurrence: i64, baselined: bool
}
struct BaselineEntry {
    fingerprint: const u8[:], code: const u8[:], path: const u8[:], occurrence: i64,
    message: const u8[:], context: const u8[:], matched: bool
}
struct FingerprintRow { identity: const u8[:], diagnostic_index: i64, start_byte: i64 }

fn fingerprint_row_less(a: FingerprintRow&, b: FingerprintRow&) -> bool {
    if a.identity != b.identity { return bytewise_less(a.identity, b.identity); }
    if a.start_byte != b.start_byte { return a.start_byte < b.start_byte; }
    return a.diagnostic_index < b.diagnostic_index;
}
struct SpecializationFact {
    id: i64, file_id: i64, path: const u8[:],
    start_byte: i64, end_byte: i64, start_line: i64, end_line: i64,
    start_column: i64, end_column: i64, precision: const u8[:],
    name: const u8[:], context: const u8[:], reachable_known: bool, reachable: bool
}
struct CallFact {
    id: i64, specialization_id: i64, file_id: i64, path: const u8[:],
    start_byte: i64, end_byte: i64, start_line: i64, end_line: i64, start_column: i64, end_column: i64,
    precision: const u8[:], callee_id: const u8[:], builtin_id: const u8[:], result_arity: i64, arg_count: i64, use_shape: const u8[:]
}
struct ResultUseFact { call_id: i64, result_index: i64, state: const u8[:], binding_name: const u8[:], referenced: bool }
struct CallArgumentFact {
    call_id: i64, index: i64, shape: const u8[:], variable_id: const u8[:], nested_call_id: i64
}
struct ContractApi {
    callee: const u8[:], role: const u8[:], owner_arg: i64, view_arg: i64,
    append_arg: i64, index_arg: i64
}
struct SeverityOverride { code: const u8[:], severity: const u8[:] }
struct PureValueFact {
    id: i64, specialization_id: i64, file_id: i64, path: const u8[:],
    start_byte: i64, end_byte: i64, start_line: i64, end_line: i64,
    expression_kind: const u8[:], proof: const u8[:]
}
struct OverflowGuardFact {
    id: i64, specialization_id: i64, file_id: i64, path: const u8[:],
    operation: const u8[:], signed: bool, width: i64,
    right_nonnegative: bool, result_matches: bool, source_matches: bool,
    relation: const u8[:], result_name: const u8[:], source_name: const u8[:],
    arithmetic_start: i64, arithmetic_end: i64, arithmetic_line: i64, arithmetic_end_line: i64,
    arithmetic_start_column: i64, arithmetic_end_column: i64,
    guard_start: i64, guard_end: i64, guard_line: i64, guard_end_line: i64,
    guard_start_column: i64, guard_end_column: i64
}
struct SliceLengthFact {
    id: i64, specialization_id: i64, file_id: i64, path: const u8[:],
    view_name: const u8[:], root_name: const u8[:],
    capture_before_growth: bool, growth_before_use: bool, same_root: bool,
    index_uses_current_length: bool,
    capture_start: i64, capture_end: i64, capture_line: i64, capture_start_column: i64, capture_end_column: i64,
    growth_start: i64, growth_end: i64, growth_line: i64, growth_start_column: i64, growth_end_column: i64,
    use_start: i64, use_end: i64, use_line: i64, use_end_line: i64,
    use_start_column: i64, use_end_column: i64
}

var saved_strings: u8[>..] = [];
var entry_facts: (const u8[:])[>..] = [];
var source_facts: SourceFact[>..] = [];
var warning_facts: WarningFact[>..] = [];
var statement_facts: StatementFact[>..] = [];
var comment_facts: CommentFact[>..] = [];
var coverage_facts: CoverageFact[>..] = [];
var analysis_facts: (const u8[:])[>..] = [];
var specialization_facts: SpecializationFact[>..] = [];
var call_facts: CallFact[>..] = [];
var result_use_facts: ResultUseFact[>..] = [];
var call_argument_facts: CallArgumentFact[>..] = [];
var call_argument_counts: i64[>..] = [];
var contract_apis: ContractApi[>..] = [];
var project_contracts_required = false;
var configured_severities: SeverityOverride[>..] = [];
var pure_value_facts: PureValueFact[>..] = [];
var overflow_guard_facts: OverflowGuardFact[>..] = [];
var slice_length_facts: SliceLengthFact[>..] = [];
var candidate_facts: OutputDiagnostic[>..] = [];
var baseline_entries: BaselineEntry[>..] = [];
var directive_states: DirectiveState[>..] = [];
var groups: (const u8[:])[>..] = [];
var allow: (const u8[:])[>..] = [];
var deny: (const u8[:])[>..] = [];
var configured_groups: (const u8[:])[>..] = [];
var enabled: (const u8[:])[>..] = [];
var config_allow: (const u8[:])[>..] = [];
var config_deny: (const u8[:])[>..] = [];

fn keep(s: const u8[:]) -> const u8[:] {
    let start = saved_strings.len;
    saved_strings.append(s);
    return saved_strings[start..];
}

fn object_count(n: json::Node?, expected: i64) -> bool {
    guard n else { return false; }
    match n.val {
        Obj o => { return o.count == expected; },
        _ => { return false; },
    }
}

fn unique_object_keys(n: json::Node?) -> bool {
    guard n else { return false; }
    match n.val {
        Obj => {
            var member = n.first;
            while member {
                var other = member.next;
                while other { if member.key == other.key { return false; } other .= other.next; }
                member .= member.next;
            }
            return true;
        },
        _ => { return false; },
    }
}

fn string_field(n: json::Node?, key: const u8[:]) -> const u8[:], bool {
    return json::as_string(json::member(n, key));
}

fn int_field(n: json::Node?, key: const u8[:]) -> i64, bool {
    return json::as_i64(json::member(n, key));
}

fn bool_field(n: json::Node?, key: const u8[:]) -> bool, bool {
    return json::as_bool(json::member(n, key));
}

fn is_null(n: json::Node?) -> bool {
    guard n else { return false; }
    match n.val { Null => { return true; }, _ => { return false; } }
}

fn contains_byte(s: const u8[:], byte: u8) -> bool {
    for c in s { if c == byte { return true; } }
    return false;
}

fn continuation(c: u8) -> bool { c >= 0x80 && c <= 0xbf }

fn valid_utf8(s: const u8[:]) -> bool {
    var i = 0;
    while i < s.len {
        let c = s[i];
        if c < 0x80 { i++; continue; }
        if c >= 0xc2 && c <= 0xdf {
            if i + 1 >= s.len || !continuation(s[i + 1]) { return false; }
            i += 2; continue;
        }
        if c == 0xe0 {
            if i + 2 >= s.len || s[i + 1] < 0xa0 || s[i + 1] > 0xbf || !continuation(s[i + 2]) { return false; }
            i += 3; continue;
        }
        if (c >= 0xe1 && c <= 0xec) || (c >= 0xee && c <= 0xef) {
            if i + 2 >= s.len || !continuation(s[i + 1]) || !continuation(s[i + 2]) { return false; }
            i += 3; continue;
        }
        if c == 0xed {
            if i + 2 >= s.len || s[i + 1] < 0x80 || s[i + 1] > 0x9f || !continuation(s[i + 2]) { return false; }
            i += 3; continue;
        }
        if c == 0xf0 {
            if i + 3 >= s.len || s[i + 1] < 0x90 || s[i + 1] > 0xbf || !continuation(s[i + 2]) || !continuation(s[i + 3]) { return false; }
            i += 4; continue;
        }
        if c >= 0xf1 && c <= 0xf3 {
            if i + 3 >= s.len || !continuation(s[i + 1]) || !continuation(s[i + 2]) || !continuation(s[i + 3]) { return false; }
            i += 4; continue;
        }
        if c == 0xf4 {
            if i + 3 >= s.len || s[i + 1] < 0x80 || s[i + 1] > 0x8f || !continuation(s[i + 2]) || !continuation(s[i + 3]) { return false; }
            i += 4; continue;
        }
        return false;
    }
    return true;
}

fn bytewise_less(a: const u8[:], b: const u8[:]) -> bool {
    let n = if a.len < b.len { a.len } else { b.len };
    for i in n { if a[i] != b[i] { return a[i] < b[i]; } }
    return a.len < b.len;
}

fn nullable_int(n: json::Node?) -> bool {
    guard n else { return false; }
    match n.val { Null => { return true; }, Int => { return true; }, _ => { return false; } }
}

fn valid_path(path: const u8[:]) -> bool {
    if path.len == 0 || path[0] == '/' || contains_byte(path, '\\') || contains_byte(path, ':') { return false; }
    var part = 0;
    for i in 0..path.len + 1 {
        if i == path.len || path[i] == '/' {
            if i == part { return false; }
            let component = path[part..i];
            if component == "." || component == ".." { return false; }
            part = i + 1;
        }
    }
    return true;
}

fn whitespace(c: u8) -> bool { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }

fn trim_space(s: const u8[:]) -> const u8[:] {
    var start = 0; var end = s.len;
    while start < end && whitespace(s[start]) { start++; }
    while end > start && whitespace(s[end - 1]) { end--; }
    return s[start..end];
}

fn parse_directive(text: const u8[:]) -> bool, const u8[:], const u8[:], const u8[:] {
    let marker = "goose-lint:";
    let at = text.find(marker);
    if at < 0 { return false, "", "", ""; }
    let body = trim_space(text[at + marker.len..]);
    if body.len < 8 || body[..6] != "allow[" { return false, "", "", "expected allow[rule_id] -- reason"; }
    let close = body.find("]");
    if close <= 6 || close + 1 >= body.len {
        return false, "", "", "expected allow[rule_id] -- reason";
    }
    let code = trim_space(body[6..close]);
    let suffix = trim_space(body[close + 1..]);
    if suffix.len < 4 || suffix[..2] != "--" { return false, "", "", "expected allow[rule_id] -- reason"; }
    let reason = trim_space(suffix[2..]);
    if !known_rule(code) { return false, code, reason, "suppression names an unknown rule ID"; }
    if reason.len == 0 { return false, code, reason, "suppression requires a nonempty reason"; }
    return true, code, reason, "";
}

fn target_statement(comment: CommentFact&) -> i64 {
    var best = -1; var best_end = -1; var ties = 0;
    for statement, index in statement_facts {
        if statement.file_id != comment.file_id { continue; }
        if statement.end_line == comment.line && statement.end_byte <= comment.start_byte {
            if statement.end_byte > best_end { best = index; best_end = statement.end_byte; ties = 1; }
            else if statement.end_byte == best_end { ties++; }
        }
    }
    if best >= 0 { return if ties == 1 { best } else { -1 }; }
    var best_start = 9223372036854775807; ties = 0; best = -1;
    for statement, index in statement_facts {
        if statement.file_id != comment.file_id || statement.start_line != comment.line + 1 { continue; }
        if statement.start_byte < best_start { best = index; best_start = statement.start_byte; ties = 1; }
        else if statement.start_byte == best_start { ties++; }
    }
    if ties == 1 { return best; }
    return -1;
}

fn warning_in_statement(warning: WarningFact&, statement: StatementFact&) -> bool {
    if warning.file_id != statement.file_id { return false; }
    if warning.precision == "exact" { return warning.start_byte >= statement.start_byte && warning.end_byte <= statement.end_byte; }
    return warning.start_line >= statement.start_line && warning.start_line <= statement.end_line;
}

fn diagnostic_in_statement(diagnostic: OutputDiagnostic&, statement: StatementFact&) -> bool {
    if diagnostic.file_id != statement.file_id { return false; }
    if diagnostic.precision == "exact" { return diagnostic.start_byte >= statement.start_byte && diagnostic.end_byte <= statement.end_byte; }
    return diagnostic.start_line >= statement.start_line && diagnostic.start_line <= statement.end_line;
}

fn directive_state(comment: CommentFact&) -> DirectiveState {
    let parsed, code, reason, message = parse_directive(comment.text);
    if !parsed { return DirectiveState { valid: false, code: keep(code), reason: keep(reason), message: keep(message), statement_index: -1 }; }
    let statement_index = target_statement(comment);
    if statement_index < 0 {
        return DirectiveState { valid: false, code: keep(code), reason: keep(reason), message: "suppression does not bind to one statement", statement_index: -1 };
    }
    let target = statement_facts[statement_index];
    var matched = false;
    for diagnostic in candidate_facts {
        if diagnostic.code == code && diagnostic_in_statement(diagnostic, target) { matched = true; }
    }
    if !matched { return DirectiveState { valid: false, code: keep(code), reason: keep(reason), message: "suppression has no matching finding", statement_index: statement_index }; }
    return DirectiveState { valid: true, code: keep(code), reason: keep(reason), message: "", statement_index: statement_index };
}

fn matching_suppression(diagnostic: OutputDiagnostic&) -> i64 {
    for state, index in directive_states {
        if !state.valid || state.code != diagnostic.code { continue; }
        if diagnostic_in_statement(diagnostic, statement_facts[state.statement_index]) { return index; }
    }
    return -1;
}

fn stale_suppression_diagnostic(comment: CommentFact&, state: DirectiveState&) -> OutputDiagnostic {
    var message: u8[>..] = [];
    format(message, "invalid goose-lint suppression: ", state.message);
    var evidence: u8[>..] = [];
    evidence.append("{\"directive\":"); json::format_string(evidence, comment.text);
    evidence.append(",\"reason\":"); json::format_string(evidence, state.message);
    if state.code.len > 0 { evidence.append(",\"rule_id\":"); json::format_string(evidence, state.code); }
    evidence.push('}');
    return make_diagnostic("stale_suppression", message, comment.file_id,
        comment.start_byte, comment.end_byte, comment.line, 0, comment.line, 0,
        "exact", evidence, "[]");
}

fn known_rule(code: const u8[:]) -> bool {
    return code == "redundant_cast" || code == "redundant_reference_marker" ||
           code == "avoidable_reference_copy" || code == "discarded_failure" ||
           code == "unchecked_poll_result" || code == "unused_pure_value" ||
           code == "stale_suppression" || code == "post_overflow_guard" ||
           code == "stale_slice_length" || code == "specialization_fanout" ||
           code == "view_before_append_argument" || code == "foreign_container_index" ||
           code == "stale_baseline";
}

fn known_group(group: const u8[:]) -> bool {
    return group == "existing" || group == "correctness" || group == "suspicious" ||
           group == "review" || group == "performance" || group == "project";
}

fn runnable_rule(code: const u8[:]) -> bool {
    return code == "redundant_cast" || code == "redundant_reference_marker" ||
           code == "avoidable_reference_copy" || code == "discarded_failure" ||
           code == "unchecked_poll_result" || code == "unused_pure_value" ||
           code == "stale_suppression" || code == "specialization_fanout" ||
           code == "post_overflow_guard" || code == "stale_slice_length" ||
           code == "view_before_append_argument" || code == "foreign_container_index" ||
           code == "stale_baseline";
}

fn contains_value(items: (const u8[:])[>..]&, value: const u8[:]) -> bool {
    for item in items { if item == value { return true; } }
    return false;
}

fn read_group_list(node: json::Node?, groups: (const u8[:])[>..]&, error: u8[>..]&) -> bool {
    guard node else { error.append("config default_groups is missing"); return false; }
    match node.val { Arr => {}, _ => { error.append("config default_groups must be an array"); return false; } }
    var ok = true;
    json::each(node) { item =>
        let name, is_string = json::as_string(item);
        if ok {
            if !is_string || !known_group(name) { error.append("config contains an unknown group"); ok = false; }
            else if contains_value(groups, name) { error.append("config contains a duplicate group"); ok = false; }
            else { groups.push(keep(name)); }
        }
    };
    return ok;
}

fn read_rule_list(node: json::Node?, name: const u8[:], rules: (const u8[:])[>..]&, error: u8[>..]&) -> bool {
    guard node else { error.append("config rule list is missing"); return false; }
    match node.val { Arr => {}, _ => { error.append("config rule lists must be arrays"); return false; } }
    var ok = true;
    json::each(node) { item =>
        let code, is_string = json::as_string(item);
        if ok {
            if !is_string || !known_rule(code) { error.append("config contains an unknown rule ID in "); error.append(name); ok = false; }
            else if !runnable_rule(code) { error.append("config selects an unavailable rule ID in "); error.append(name); ok = false; }
            else if contains_value(rules, code) { error.append("config contains a duplicate rule ID in "); error.append(name); ok = false; }
            else { rules.push(keep(code)); }
        }
    };
    return ok;
}

fn load_config(path: const u8[:], groups: (const u8[:])[>..]&, enabled: (const u8[:])[>..]&,
               allow: (const u8[:])[>..]&, deny: (const u8[:])[>..]&, baseline: u8[>..]&, 
               contracts: u8[>..]&, severities: SeverityOverride[>..]&, error: u8[>..]&) -> bool {
    var input: u8[>..] = [];
    if !read_file(path, input) { error.append("cannot read --config file"); return false; }
    if input.len == 0 || input.len > 1048576 { error.append("config is empty or exceeds 1 MiB"); return false; }
    var doc: json::Node[>..] = [];
    var decoded: u8[>..] = [];
    let root, parse_error = json::parse(input, doc, decoded);
    guard root else { error.append("config is invalid JSON: "); error.append(parse_error); return false; }
    if parse_error.len != 0 { error.append("config is invalid JSON: "); error.append(parse_error); return false; }
    match root.val { Obj => {}, _ => { error.append("config root must be an object"); return false; } }
    var count = 0; var version_seen = false; var groups_seen = false;
    var enabled_seen = false; var allow_seen = false; var deny_seen = false;
    var baseline_seen = false; var contracts_seen = false; var severity_seen = false;
    var member = root.first;
    while member {
        count++;
        var other = member.next;
        while other { if member.key == other.key { error.append("config contains a duplicate key"); return false; } other .= other.next; }
        if member.key == "schema_version" { version_seen = true; }
        else if member.key == "default_groups" { groups_seen = true; }
        else if member.key == "enable" { enabled_seen = true; }
        else if member.key == "allow" { allow_seen = true; }
        else if member.key == "deny" { deny_seen = true; }
        else if member.key == "baseline" { baseline_seen = true; }
        else if member.key == "contracts" { contracts_seen = true; }
        else if member.key == "severity" { severity_seen = true; }
        else if member.key == "review" {
            error.append("config field is not supported by this companion build: "); error.append(member.key); return false;
        } else { error.append("unknown config field: "); error.append(member.key); return false; }
        member .= member.next;
    }
    if count > 8 || !version_seen { error.append("config requires schema_version and supports at most eight fields"); return false; }
    let version, version_ok = int_field(root, "schema_version");
    if !version_ok || version != 1 { error.append("config schema_version must be 1"); return false; }
    if groups_seen && !read_group_list(json::member(root, "default_groups"), groups, error) { return false; }
    if enabled_seen && !read_rule_list(json::member(root, "enable"), "enable", enabled, error) { return false; }
    if allow_seen && !read_rule_list(json::member(root, "allow"), "allow", allow, error) { return false; }
    if deny_seen && !read_rule_list(json::member(root, "deny"), "deny", deny, error) { return false; }
    if baseline_seen {
        let value, value_ok = string_field(root, "baseline");
        if !value_ok || value.len == 0 { error.append("config baseline must be a nonempty path"); return false; }
        baseline.append(value);
    }
    if contracts_seen {
        let value, value_ok = string_field(root, "contracts");
        if !value_ok || value.len == 0 { error.append("config contracts must be a nonempty path"); return false; }
        contracts.append(value);
    }
    if severity_seen {
        let overrides = json::member(root, "severity");
        guard overrides else { error.append("config severity must be an object"); return false; }
        if !unique_object_keys(overrides) { error.append("config severity must have unique rule IDs"); return false; }
        match overrides.val { Obj => {}, _ => { error.append("config severity must be an object"); return false; } }
        var setting = overrides.first;
        while setting {
            if !known_rule(setting.key) || !runnable_rule(setting.key) {
                error.append("config severity contains an unknown or unavailable rule ID: ");
                error.append(setting.key);
                return false;
            }
            let value, value_ok = string_field(overrides, setting.key);
            if !value_ok || (value != "error" && value != "warning" && value != "note") {
                error.append("config severity must be error, warning, or note for rule ");
                error.append(setting.key);
                return false;
            }
            severities.push(SeverityOverride { code: keep(setting.key), severity: keep(value) });
            setting .= setting.next;
        }
    }
    for code in allow { if contains_value(deny, code) { error.append("config rule cannot be both allowed and denied: "); error.append(code); return false; } }
    return true;
}

fn load_contracts(path: const u8[:], error: u8[>..]&) -> bool {
    contract_apis.clear();
    if path.len == 0 { return true; }
    var input: u8[>..] = [];
    if !read_file(path, input) { error.append("cannot read contracts file"); return false; }
    if input.len == 0 || input.len > 1048576 { error.append("contracts file is empty or exceeds 1 MiB"); return false; }
    var doc: json::Node[>..] = [];
    var decoded: u8[>..] = [];
    let root, parse_error = json::parse(input, doc, decoded);
    guard root else { error.append("contracts file is invalid JSON: "); error.append(parse_error); return false; }
    if parse_error.len != 0 { error.append("contracts file is invalid JSON: "); error.append(parse_error); return false; }
    if !object_count(root, 2) || !unique_object_keys(root) { error.append("contracts root must contain schema_version and apis exactly once"); return false; }
    let version, version_ok = int_field(root, "schema_version");
    let apis = json::member(root, "apis");
    if !version_ok || version != 1 || !apis { error.append("contracts require schema_version 1 and an apis array"); return false; }
    match apis.val { Arr => {}, _ => { error.append("contracts apis must be an array"); return false; } }
    json::each(apis) { item =>
        if !unique_object_keys(item) { error.append("contract entry must be an object with unique keys"); return false from load_contracts; }
        let callee, callee_ok = string_field(item, "callee");
        let role, role_ok = string_field(item, "role");
        if !callee_ok || callee.len == 0 || !role_ok { error.append("contract entry requires callee and role strings"); return false from load_contracts; }
        var owner_arg = -1; var view_arg = -1; var append_arg = -1; var index_arg = -1;
        if role == "append_to" || role == "index_of" {
            if !object_count(item, 3) { error.append("append_to and index_of contracts require exactly callee, role, and owner_arg"); return false from load_contracts; }
            let value, ok = int_field(item, "owner_arg");
            if !ok || value < 0 || value > 255 { error.append("contract owner_arg must be an index from 0 through 255"); return false from load_contracts; }
            owner_arg = value;
        } else if role == "consumes_index" {
            if !object_count(item, 4) { error.append("consumes_index contract requires exactly callee, role, owner_arg, and index_arg"); return false from load_contracts; }
            let owner, owner_ok = int_field(item, "owner_arg"); let index, index_ok = int_field(item, "index_arg");
            if !owner_ok || !index_ok || owner < 0 || owner > 255 || index < 0 || index > 255 || owner == index {
                error.append("consumes_index argument roles are invalid"); return false from load_contracts;
            }
            owner_arg = owner; index_arg = index;
        } else if role == "view_after_append" {
            if !object_count(item, 4) { error.append("view_after_append contract requires exactly callee, role, view_arg, and append_arg"); return false from load_contracts; }
            let view, view_ok = int_field(item, "view_arg"); let append, append_ok = int_field(item, "append_arg");
            if !view_ok || !append_ok || view < 0 || view > 255 || append < 0 || append > 255 || view == append {
                error.append("view_after_append argument roles are invalid"); return false from load_contracts;
            }
            view_arg = view; append_arg = append;
        } else { error.append("contracts contain an unknown API role"); return false from load_contracts; }
        for prior in contract_apis {
            if prior.callee == callee && prior.role == role { error.append("contracts contain a duplicate callee role"); return false from load_contracts; }
        }
        contract_apis.push(ContractApi { callee: keep(callee), role: keep(role), owner_arg: owner_arg,
            view_arg: view_arg, append_arg: append_arg, index_arg: index_arg });
    };
    stable_sort(contract_apis) { a, b => if a.callee == b.callee { bytewise_less(a.role, b.role) } else { bytewise_less(a.callee, b.callee) } };
    return true;
}

fn contract_api_index(callee: const u8[:], role: const u8[:]) -> i64 {
    for api, index in contract_apis { if api.callee == callee && api.role == role { return index; } }
    return -1;
}

fn resolved_call_name(call: CallFact&) -> const u8[:] {
    return if call.callee_id.len > 0 { call.callee_id } else { call.builtin_id };
}

fn call_argument_record(call_id: i64, index: i64) -> i64 {
    for argument, record_index in call_argument_facts {
        if argument.call_id == call_id && argument.index == index { return record_index; }
    }
    return -1;
}

fn argument_variable(call_id: i64, index: i64) -> const u8[:] {
    let record_index = call_argument_record(call_id, index);
    if record_index < 0 { return ""; }
    let argument = call_argument_facts[record_index];
    if argument.shape == "identifier" || argument.shape == "slice" { return argument.variable_id; }
    return "";
}

fn argument_shape(call_id: i64, index: i64) -> const u8[:] {
    let record_index = call_argument_record(call_id, index);
    return if record_index < 0 { "missing" } else { call_argument_facts[record_index].shape };
}

fn argument_nested_call(call_id: i64, index: i64) -> i64 {
    let record_index = call_argument_record(call_id, index);
    if record_index < 0 { return -1; }
    let argument = call_argument_facts[record_index];
    return if argument.shape == "call" { argument.nested_call_id } else { -1 };
}

fn validate_contract_calls(error: u8[>..]&) -> bool {
    for call in call_facts {
        let identity = resolved_call_name(call);
        for api in contract_apis {
            if api.callee != identity { continue; }
            if ((api.role == "append_to" || api.role == "index_of" || api.role == "consumes_index") && api.owner_arg >= call.arg_count) ||
               (api.role == "consumes_index" && api.index_arg >= call.arg_count) ||
               (api.role == "view_after_append" && (api.view_arg >= call.arg_count || api.append_arg >= call.arg_count)) {
                error.append("contract argument index exceeds the resolved API arity: "); error.append(api.callee); return false;
            }
        }
    }
    return true;
}

fn hash_bytes(hash: u64, bytes: const u8[:]) -> u64 {
    var h = hash;
    for c in bytes { h ^= c; h *= 1099511628211; }
    return h;
}

fn hash_line(hash: u64, bytes: const u8[:]) -> u64 {
    var h = hash_bytes(hash, bytes);
    h ^= 10;
    h *= 1099511628211;
    return h;
}

fn hash_text(hash: u64) -> u8[>..] {
    var out: u8[>..] = [];
    out.append("fnv1a64:");
    format_uint(out, hash, 16, 16, '0');
    return out;
}

fn baseline_context(diagnostic: OutputDiagnostic&) -> const u8[:] {
    var context: u8[>..] = [];
    context.append(diagnostic.evidence_json);
    context.push(0);
    context.append(diagnostic.specialization_json);
    return keep(context);
}

fn baseline_identity(diagnostic: OutputDiagnostic&, facts: Facts&) -> const u8[:] {
    var identity: u8[>..] = [];
    identity.append(diagnostic.code); identity.push(0);
    identity.append(source_at(facts, diagnostic.file_id)); identity.push(0);
    identity.append(diagnostic.message); identity.push(0);
    identity.append(baseline_context(diagnostic));
    return keep(identity);
}

fn baseline_fingerprint(identity: const u8[:], occurrence: i64) -> const u8[:] {
    var bytes: u8[>..] = [];
    bytes.append("goose-lint-fingerprint-v1\0");
    bytes.append(identity); bytes.push(0);
    format(bytes, occurrence);
    return keep(hash_text(hash_bytes(14695981039346656037, bytes)));
}

fn assign_fingerprints(diagnostics: OutputDiagnostic[>..]&, facts: Facts&) {
    var rows: FingerprintRow[>..] = [];
    for diagnostic, index in diagnostics {
        if diagnostic.code == "stale_suppression" { continue; }
        rows.push(FingerprintRow { identity: baseline_identity(diagnostic, facts),
            diagnostic_index: index, start_byte: if diagnostic.precision == "exact" { diagnostic.start_byte } else { -1 } });
    }
    stable_sort(rows) { a, b => fingerprint_row_less(a, b) };
    var previous: const u8[:] = "";
    var occurrence = 0;
    for row in rows {
        if row.identity != previous { previous = row.identity; occurrence = 0; }
        else { occurrence++; }
        let diagnostic = &diagnostics[row.diagnostic_index];
        diagnostic.baseline_occurrence = occurrence;
        diagnostic.baseline_fingerprint = baseline_fingerprint(row.identity, occurrence);
    }
}

fn valid_fingerprint(value: const u8[:]) -> bool {
    if value.len != 24 || value[..8] != "fnv1a64:" { return false; }
    for c in value[8..] {
        if !((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) { return false; }
    }
    return true;
}

fn load_baseline(path: const u8[:], error: u8[>..]&) -> bool {
    baseline_entries.clear();
    var input: u8[>..] = [];
    if !read_file(path, input) { error.append("cannot read --baseline file"); return false; }
    if input.len == 0 || input.len > 16777216 { error.append("baseline is empty or exceeds 16 MiB"); return false; }
    var doc: json::Node[>..] = [];
    var decoded: u8[>..] = [];
    let root, parse_error = json::parse(input, doc, decoded);
    guard root else { error.append("baseline is invalid JSON: "); error.append(parse_error); return false; }
    if parse_error.len != 0 { error.append("baseline is invalid JSON: "); error.append(parse_error); return false; }
    if !object_count(root, 3) || !unique_object_keys(root) { error.append("baseline root has an invalid shape or duplicate key"); return false; }
    let version, version_ok = int_field(root, "schema_version");
    let fingerprint_version, fingerprint_ok = int_field(root, "fingerprint_version");
    let entries = json::member(root, "entries");
    if !version_ok || version != 1 || !fingerprint_ok || fingerprint_version != 1 || !entries {
        error.append("baseline requires schema_version 1, fingerprint_version 1, and entries"); return false;
    }
    match entries.val { Arr => {}, _ => { error.append("baseline entries must be an array"); return false; } }
    var valid = true;
    json::each(entries) { item =>
        if valid {
            if !object_count(item, 6) || !unique_object_keys(item) { error.append("baseline entry has an invalid shape or duplicate key"); valid = false; }
            else {
                let fingerprint, fingerprint_ok = string_field(item, "fingerprint");
                let code, code_ok = string_field(item, "code");
                let path_value, path_ok = string_field(item, "path");
                let occurrence, occurrence_ok = int_field(item, "occurrence");
                let message, message_ok = string_field(item, "message");
                let context, context_ok = string_field(item, "context");
                if !fingerprint_ok || !valid_fingerprint(fingerprint) || !code_ok || !known_rule(code) ||
                   !path_ok || !valid_path(path_value) || !occurrence_ok || occurrence < 0 ||
                   !message_ok || !context_ok {
                    error.append("baseline entry has invalid fields"); valid = false;
                } else {
                    var identity: u8[>..] = [];
                    identity.append(code); identity.push(0); identity.append(path_value); identity.push(0);
                    identity.append(message); identity.push(0); identity.append(context);
                    if baseline_fingerprint(identity, occurrence) != fingerprint {
                        error.append("baseline entry fingerprint does not match its contents"); valid = false;
                    } else {
                        baseline_entries.push(BaselineEntry { fingerprint: keep(fingerprint), code: keep(code),
                            path: keep(path_value), occurrence: occurrence, message: keep(message),
                            context: keep(context), matched: false });
                    }
                }
            }
        }
    };
    if !valid { baseline_entries.clear(); return false; }
    stable_sort(baseline_entries) { a, b => bytewise_less(a.fingerprint, b.fingerprint) };
    for i in 1..baseline_entries.len {
        if baseline_entries[i - 1].fingerprint == baseline_entries[i].fingerprint {
            error.append("baseline contains a duplicate or colliding fingerprint"); baseline_entries.clear(); return false;
        }
    }
    return true;
}

fn find_baseline(fingerprint: const u8[:]) -> i64 {
    var low = 0; var high = baseline_entries.len;
    while low < high {
        let mid = low + (high - low) / 2;
        if bytewise_less(baseline_entries[mid].fingerprint, fingerprint) { low = mid + 1; }
        else { high = mid; }
    }
    if low < baseline_entries.len && baseline_entries[low].fingerprint == fingerprint { return low; }
    return -1;
}

fn apply_baseline(diagnostics: OutputDiagnostic[>..]&, facts: Facts&, error: u8[>..]&) -> i64 {
    var stale = 0;
    for i in diagnostics.len {
        let diagnostic = &diagnostics[i];
        if diagnostic.baseline_fingerprint.len == 0 { continue; }
        let index = find_baseline(diagnostic.baseline_fingerprint);
        if index < 0 { continue; }
        let entry = &baseline_entries[index];
        let context = baseline_context(diagnostic);
        if entry.code != diagnostic.code || entry.path != source_at(facts, diagnostic.file_id) ||
           entry.occurrence != diagnostic.baseline_occurrence || entry.message != diagnostic.message ||
           entry.context != context {
            error.append("baseline fingerprint collision detected"); return -1;
        }
        entry.matched = true;
        diagnostic.baselined = true;
    }
    for entry in baseline_entries { if !entry.matched { stale++; } }
    return stale;
}

fn write_baseline_file(path: const u8[:], diagnostics: OutputDiagnostic[>..]&, facts: Facts&) -> bool {
    var out: u8[>..] = [];
    out.append("{\"schema_version\":1,\"fingerprint_version\":1,\"entries\":[");
    var selected: OutputDiagnostic[>..] = [];
    for diagnostic in diagnostics {
        if diagnostic.baseline_fingerprint.len > 0 { selected.push(diagnostic); }
    }
    stable_sort(selected) { a, b => bytewise_less(a.baseline_fingerprint, b.baseline_fingerprint) };
    var first = true;
    for diagnostic in selected {
        if !first { out.push(','); } first = false;
        out.append("{\"fingerprint\":"); json::format_string(out, diagnostic.baseline_fingerprint);
        out.append(",\"code\":"); json::format_string(out, diagnostic.code);
        out.append(",\"path\":"); json::format_string(out, source_at(facts, diagnostic.file_id));
        format(out, ",\"occurrence\":", diagnostic.baseline_occurrence);
        out.append(",\"message\":"); json::format_string(out, diagnostic.message);
        out.append(",\"context\":"); json::format_string(out, baseline_context(diagnostic));
        out.push('}');
    }
    out.append("]}\n");
    return write_file_atomic(path, out);
}

fn baseline_count(diagnostics: OutputDiagnostic[>..]&) -> i64 {
    var count = 0;
    for diagnostic in diagnostics { if diagnostic.baseline_fingerprint.len > 0 { count++; } }
    return count;
}

fn source_at(facts: Facts&, file_id: i64) -> const u8[:] {
    if file_id < 0 || file_id >= source_facts.len { return "<unknown>"; }
    return source_facts[file_id].path;
}

fn valid_record_shape(root: json::Node?, kind: const u8[:]) -> bool {
    if kind == "header" { return object_count(root, 7); }
    if kind == "source" { return object_count(root, 6); }
    if kind == "warning" { return object_count(root, 6); }
    if kind == "statement" { return object_count(root, 8); }
    if kind == "comment" { return object_count(root, 9); }
    if kind == "specialization" { return object_count(root, 14); }
    if kind == "call" { return object_count(root, 17); }
    if kind == "result_use" { return object_count(root, 6); }
    if kind == "call_argument" { return object_count(root, 6); }
    if kind == "pure_value" { return object_count(root, 11); }
    if kind == "overflow_guard" { return object_count(root, 26); }
    if kind == "slice_length" { return object_count(root, 27); }
    if kind == "coverage" { return object_count(root, 8); }
    if kind == "end" { return object_count(root, 3); }
    return false;
}

fn parse_facts(input: const u8[:], facts: Facts&, error: u8[>..]&) -> bool {
    entry_facts.clear(); source_facts.clear(); warning_facts.clear(); statement_facts.clear();
    comment_facts.clear(); coverage_facts.clear(); analysis_facts.clear();
    specialization_facts.clear(); call_facts.clear(); result_use_facts.clear(); call_argument_facts.clear();
    call_argument_counts.clear(); pure_value_facts.clear();
    overflow_guard_facts.clear(); slice_length_facts.clear();
    if input.len == 0 || input.len > MAX_FACTS { error.append("facts stream is empty or exceeds 64 MiB"); return false; }
    if !valid_utf8(input) { error.append("facts stream contains invalid UTF-8"); return false; }
    if input[input.len - 1] != '\n' { error.append("facts stream is missing its final LF"); return false; }
    var hash: u64 = 14695981039346656037;
    var offset = 0;
    var records = 0;
    var phase = 0;
    var expected_warning = 0;
    var expected_comment = 0;
    var expected_source = 0;
    var expected_coverage = 0;
    var saw_end = false;
    var previous_warning_path: const u8[:] = ""; var previous_warning_start = 0;
    var previous_warning_code: const u8[:] = ""; var previous_warning_message: const u8[:] = "";
    var have_previous_warning = false;
    var previous_statement_file = -1; var previous_statement_start = 0;
    var previous_statement_end = 0; var previous_statement_order = 0;
    var have_previous_statement = false;
    var previous_comment_file = -1; var previous_comment_start = 0; var previous_comment_end = 0;
    var have_previous_comment = false;
    var previous_specialization_path: const u8[:] = ""; var previous_specialization_line = 0;
    var previous_specialization_name: const u8[:] = ""; var previous_specialization_context: const u8[:] = "";
    var have_previous_specialization = false;
    var previous_call_specialization = -1; var previous_call_path: const u8[:] = "";
    var previous_call_start = 0; var previous_call_use: const u8[:] = ""; var have_previous_call = false;
    var previous_result_call = -1; var previous_result_index = -1; var have_previous_result = false;
    var expected_pure_value = 0;
    var previous_pure_file = -1; var previous_pure_start = 0; var previous_pure_specialization = -1;
    var have_previous_pure = false;
    while offset < input.len {
        let start = offset;
        while offset < input.len && input[offset] != '\n' { offset++; }
        let line = input[start..offset];
        if offset - start > MAX_RECORD { error.append("facts record exceeds 16 MiB"); return false; }
        if line.len == 0 || contains_byte(line, '\r') { error.append("facts contains an empty or CR-terminated record"); return false; }
        offset++;
        records++;
        if records > MAX_RECORDS { error.append("facts stream exceeds one million records"); return false; }
        var doc: json::Node[>..] = [];
        var decoded: u8[>..] = [];
        let root, parse_error = json::parse(line, doc, decoded);
        guard root else { error.append("facts record is invalid JSON: "); error.append(parse_error); return false; }
        if parse_error.len != 0 { error.append("facts record is invalid JSON: "); error.append(parse_error); return false; }
        let kind, kind_ok = string_field(root, "kind");
        if !kind_ok || !valid_record_shape(root, kind) { error.append("facts record has an unknown kind or wrong field count"); return false; }
        if saw_end { error.append("facts end record is not terminal"); return false; }

        if kind == "header" {
            if records != 1 || phase != 0 { error.append("facts header must be the first record"); return false; }
            let version, version_ok = int_field(root, "facts_version");
            let compiler, compiler_ok = string_field(root, "compiler");
            let revision, revision_ok = string_field(root, "compiler_revision");
            let profile, profile_ok = string_field(root, "profile");
            if !version_ok || version != 1 || !compiler_ok || compiler != "goose" || !revision_ok ||
               revision.len == 0 || !profile_ok || (profile != "O0" && profile != "O1" && profile != "O2") {
                error.append("facts header version, compiler, revision, or profile is invalid"); return false;
            }
            let entries = json::member(root, "entries");
            guard entries else { error.append("facts header entries is missing"); return false; }
            match entries.val { Arr a => { if a.count != 1 { error.append("facts header must contain exactly one entry"); return false; } }, _ => { error.append("facts header entries is not an array"); return false; } }
            json::each(entries) { e =>
                let value, ok = json::as_string(e);
                if !ok || !valid_path(value) { error.append("facts header contains an invalid entry path"); return false from parse_facts; }
                entry_facts.push(keep(value));
            };
            let options = json::member(root, "frontend_options");
            guard options else { error.append("facts frontend_options is missing"); return false; }
            if !object_count(options, 3) { error.append("facts frontend_options has an invalid shape"); return false; }
            let debug, debug_ok = bool_field(options, "debug");
            let unsafe_check, unsafe_ok = bool_field(options, "unsafe_no_rf_check");
            let allow_fetch, fetch_ok = bool_field(options, "allow_fetch");
            if !debug_ok || !unsafe_ok || !fetch_ok { error.append("facts frontend_options has an invalid type"); return false; }
            facts.revision = keep(revision);
            facts.profile = keep(profile);
            phase = 1;
            hash = hash_line(hash, line);
        } else if kind == "source" {
            if phase != 1 { error.append("source facts are out of order"); return false; }
            let id, id_ok = int_field(root, "file_id");
            let path, path_ok = string_field(root, "path");
            let content_hash, hash_ok = string_field(root, "content_hash");
            let byte_length, length_ok = int_field(root, "byte_length");
            let endings, endings_ok = string_field(root, "line_endings");
            if !id_ok || id != expected_source || !path_ok || !valid_path(path) || !hash_ok ||
               content_hash.len != 24 || content_hash[..8] != "fnv1a64:" || !length_ok || byte_length < 0 ||
               !endings_ok || (endings != "lf" && endings != "crlf" && endings != "cr" && endings != "mixed" && endings != "none") {
                error.append("source fact has invalid fields"); return false;
            }
            for i in 8..24 {
                let c = content_hash[i];
                if !((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f')) { error.append("source content hash is malformed"); return false; }
            }
            if expected_source > 0 && !bytewise_less(source_facts[expected_source - 1].path, path) { error.append("source paths are not uniquely sorted"); return false; }
            source_facts.push(SourceFact { path: keep(path), id: id, byte_length: byte_length });
            expected_source++;
            hash = hash_line(hash, line);
        } else if kind == "warning" {
            if phase < 1 || phase > 2 || source_facts.len == 0 { error.append("warning fact is out of order"); return false; }
            phase = 2;
            let id, id_ok = int_field(root, "id");
            let code, code_ok = string_field(root, "code");
            let message, message_ok = string_field(root, "message");
            let source = json::member(root, "source");
            let specialization_node = json::member(root, "specializations");
            guard specialization_node else { error.append("warning fact is missing specializations"); return false; }
            if !object_count(source, 9) || !id_ok || id != expected_warning || !code_ok ||
               (code != "redundant_cast" && code != "redundant_reference_marker" && code != "avoidable_reference_copy") || !message_ok {
                error.append("warning fact has invalid fields"); return false;
            }
            var specialization_json: u8[>..] = [];
            match specialization_node.val {
                Arr => {},
                _ => { error.append("warning specializations is not an array"); return false; },
            }
            specialization_json.push('[');
            var specialization_node_item = specialization_node.first;
            var previous_context: const u8[:] = "";
            var have_previous_context = false;
            while specialization_node_item {
                let context, context_ok = json::as_string(specialization_node_item);
                if !context_ok || context.len == 0 || (have_previous_context && !bytewise_less(previous_context, context)) {
                    error.append("warning specialization contexts are invalid or unsorted"); return false;
                }
                if have_previous_context { specialization_json.push(','); }
                json::format_string(specialization_json, context);
                previous_context = keep(context);
                have_previous_context = true;
                specialization_node_item .= specialization_node_item.next;
            }
            specialization_json.push(']');
            let file_node = json::member(source, "file_id");
            var file_id = -1; var file_ok = is_null(file_node);
            if !file_ok { let found_id, found_ok = json::as_i64(file_node); file_id = found_id; file_ok = found_ok; }
            let line_no, line_ok = int_field(source, "line");
            let start_line, sl_ok = int_field(source, "start_line");
            let precision, precision_ok = string_field(source, "precision");
            let start_column_node = json::member(source, "start_column");
            let end_line_node = json::member(source, "end_line");
            let end_column_node = json::member(source, "end_column");
            let start_byte_node = json::member(source, "start_byte");
            let end_byte_node = json::member(source, "end_byte");
            if !file_ok || (file_id >= source_facts.len) || (file_id < 0 && file_id != -1) || !line_ok || line_no < 1 ||
               !sl_ok || start_line < 1 || line_no != start_line || !precision_ok { error.append("warning location has invalid fields"); return false; }
            var start_column = 0; var end_line = 0; var end_column = 0; var start_byte = 0; var end_byte = 0;
            if precision == "exact" {
                let sc, sc_ok = json::as_i64(start_column_node); let el, el_ok = json::as_i64(end_line_node);
                let ec, ec_ok = json::as_i64(end_column_node); let sb, sb_ok = json::as_i64(start_byte_node);
                let eb, eb_ok = json::as_i64(end_byte_node);
                if file_id < 0 || !sc_ok || !el_ok || !ec_ok || !sb_ok || !eb_ok || sc < 1 || el < start_line || ec < 1 || sb < 0 || eb < sb || eb > source_facts[file_id].byte_length {
                    error.append("exact warning location is invalid"); return false;
                }
                start_column = sc; end_line = el; end_column = ec; start_byte = sb; end_byte = eb;
            } else if precision == "line" {
                if !is_null(start_column_node) || !is_null(end_line_node) || !is_null(end_column_node) ||
                   !is_null(start_byte_node) || !is_null(end_byte_node) { error.append("line warning location contains fabricated precision"); return false; }
            } else { error.append("warning location precision is invalid"); return false; }
            let warning_path = if file_id < 0 { "<unknown>" } else { source_facts[file_id].path };
            let sort_start = if precision == "exact" { start_byte } else { 0 };
            if have_previous_warning {
                var out_of_order = bytewise_less(warning_path, previous_warning_path);
                if warning_path == previous_warning_path {
                    out_of_order = sort_start < previous_warning_start ||
                        (sort_start == previous_warning_start && bytewise_less(code, previous_warning_code)) ||
                        (sort_start == previous_warning_start && code == previous_warning_code && bytewise_less(message, previous_warning_message));
                }
                if out_of_order { error.append("warning facts are not deterministically sorted"); return false; }
            }
            previous_warning_path = warning_path; previous_warning_start = sort_start;
            previous_warning_code = keep(code); previous_warning_message = keep(message); have_previous_warning = true;
            warning_facts.push(WarningFact { code: keep(code), message: keep(message), file_id: file_id,
                line: line_no, start_line: start_line, start_column: start_column, end_line: end_line,
                end_column: end_column, start_byte: start_byte, end_byte: end_byte, precision: keep(precision),
                specialization_json: keep(specialization_json) });
            expected_warning++;
            hash = hash_line(hash, line);
        } else if kind == "statement" {
            if phase < 1 || phase > 3 { error.append("statement fact is out of order"); return false; }
            phase = 3;
            let file_id, fid_ok = int_field(root, "file_id"); let path, path_ok = string_field(root, "path");
            let start_byte, sb_ok = int_field(root, "start_byte"); let end_byte, eb_ok = int_field(root, "end_byte");
            let start_line, sl_ok = int_field(root, "start_line"); let end_line, el_ok = int_field(root, "end_line");
            let order, order_ok = int_field(root, "source_order");
            if !fid_ok || file_id < 0 || file_id >= source_facts.len || !path_ok || path != source_facts[file_id].path ||
               !sb_ok || !eb_ok || start_byte < 0 || end_byte < start_byte || !sl_ok || !el_ok ||
               start_line < 1 || end_line < start_line || !order_ok || order < 0 { error.append("statement fact has invalid fields"); return false; }
            if have_previous_statement {
                let out_of_order = file_id < previous_statement_file ||
                    (file_id == previous_statement_file && start_byte < previous_statement_start) ||
                    (file_id == previous_statement_file && start_byte == previous_statement_start && end_byte < previous_statement_end) ||
                    (file_id == previous_statement_file && start_byte == previous_statement_start && end_byte == previous_statement_end && order < previous_statement_order);
                if out_of_order { error.append("statement facts are not deterministically sorted"); return false; }
            }
            previous_statement_file = file_id; previous_statement_start = start_byte;
            previous_statement_end = end_byte; previous_statement_order = order; have_previous_statement = true;
            statement_facts.push(StatementFact { file_id: file_id, start_byte: start_byte, end_byte: end_byte,
                start_line: start_line, end_line: end_line, source_order: order });
            hash = hash_line(hash, line);
        } else if kind == "comment" {
            if phase < 1 || phase > 4 { error.append("comment fact is out of order"); return false; }
            phase = 4;
            let id, id_ok = int_field(root, "id"); let file_id, fid_ok = int_field(root, "file_id");
            let path, path_ok = string_field(root, "path"); let start_byte, sb_ok = int_field(root, "start_byte");
            let end_byte, eb_ok = int_field(root, "end_byte"); let line_no, line_ok = int_field(root, "line");
            let form, form_ok = string_field(root, "form"); let text, text_ok = string_field(root, "text");
            if !id_ok || id != expected_comment || !fid_ok || file_id < 0 || file_id >= source_facts.len ||
               !path_ok || path != source_facts[file_id].path || !sb_ok || !eb_ok || start_byte < 0 || end_byte < start_byte ||
               !line_ok || line_no < 1 || !form_ok || (form != "line" && form != "block") || !text_ok {
                error.append("comment fact has invalid fields"); return false;
            }
            if have_previous_comment {
                let out_of_order = file_id < previous_comment_file ||
                    (file_id == previous_comment_file && start_byte < previous_comment_start) ||
                    (file_id == previous_comment_file && start_byte == previous_comment_start && end_byte < previous_comment_end);
                if out_of_order { error.append("comment facts are not deterministically sorted"); return false; }
            }
            previous_comment_file = file_id; previous_comment_start = start_byte; previous_comment_end = end_byte; have_previous_comment = true;
            comment_facts.push(CommentFact { id: id, file_id: file_id, path: keep(path), start_byte: start_byte,
                end_byte: end_byte, line: line_no, form: keep(form), text: keep(text) });
            expected_comment++;
            hash = hash_line(hash, line);
        } else if kind == "specialization" {
            if phase < 1 || phase > 5 { error.append("specialization fact is out of order"); return false; }
            phase = 5;
            let id, id_ok = int_field(root, "id"); let file_id, fid_ok = int_field(root, "file_id");
            let path, path_ok = string_field(root, "path");
            let start_line, sl_ok = int_field(root, "start_line"); let end_line, el_ok = int_field(root, "end_line");
            let precision, precision_ok = string_field(root, "precision");
            let start_byte_node = json::member(root, "start_byte"); let end_byte_node = json::member(root, "end_byte");
            let start_column_node = json::member(root, "start_column"); let end_column_node = json::member(root, "end_column");
            let name, name_ok = string_field(root, "name"); let context, context_ok = string_field(root, "context");
            let reachable_node = json::member(root, "entry_reachable");
            var reachable_known = !is_null(reachable_node); var reachable = false; var reachable_ok = true;
            if reachable_known { let value, ok = json::as_bool(reachable_node); reachable = value; reachable_ok = ok; }
            if !id_ok || id != specialization_facts.len || !fid_ok || file_id < 0 || file_id >= source_facts.len ||
               !path_ok || path != source_facts[file_id].path || !sl_ok || !el_ok || start_line < 1 || end_line < start_line ||
               !precision_ok || !name_ok || name.len == 0 || !context_ok || !reachable_ok {
                error.append("specialization fact has invalid fields"); return false;
            }
            var start_byte = 0; var end_byte = 0; var start_column = 0; var end_column = 0;
            if precision == "exact" {
                let sb, sb_ok = json::as_i64(start_byte_node); let eb, eb_ok = json::as_i64(end_byte_node);
                let sc, sc_ok = json::as_i64(start_column_node); let ec, ec_ok = json::as_i64(end_column_node);
                if !sb_ok || !eb_ok || !sc_ok || !ec_ok || sb < 0 || eb < sb || eb > source_facts[file_id].byte_length ||
                   sc < 1 || ec < 1 { error.append("exact specialization location is invalid"); return false; }
                start_byte = sb; end_byte = eb; start_column = sc; end_column = ec;
            } else if precision == "line" {
                if !is_null(start_byte_node) || !is_null(end_byte_node) ||
                   !is_null(start_column_node) || !is_null(end_column_node) || end_line != start_line {
                    error.append("line specialization location contains fabricated precision"); return false;
                }
            } else { error.append("specialization location precision is invalid"); return false; }
            if have_previous_specialization {
                let out_of_order = bytewise_less(path, previous_specialization_path) ||
                    (path == previous_specialization_path && start_line < previous_specialization_line) ||
                    (path == previous_specialization_path && start_line == previous_specialization_line && bytewise_less(name, previous_specialization_name)) ||
                    (path == previous_specialization_path && start_line == previous_specialization_line && name == previous_specialization_name && bytewise_less(context, previous_specialization_context));
                if out_of_order { error.append("specialization facts are not deterministically sorted"); return false; }
            }
            previous_specialization_path = keep(path); previous_specialization_line = start_line;
            previous_specialization_name = keep(name); previous_specialization_context = keep(context); have_previous_specialization = true;
            specialization_facts.push(SpecializationFact { id: id, file_id: file_id, path: keep(path),
                start_byte: start_byte, end_byte: end_byte, start_line: start_line, end_line: end_line,
                start_column: start_column, end_column: end_column, precision: keep(precision),
                name: keep(name), context: keep(context), reachable_known: reachable_known, reachable: reachable });
            hash = hash_line(hash, line);
        } else if kind == "call" {
            if phase < 1 || phase > 6 { error.append("call fact is out of order"); return false; }
            phase = 6;
            let id, id_ok = int_field(root, "id");
            let specialization_node = json::member(root, "specialization_id");
            var specialization_id = -1; var sid_ok = is_null(specialization_node);
            if !sid_ok { let value, ok = json::as_i64(specialization_node); specialization_id = value; sid_ok = ok; }
            let file_id, fid_ok = int_field(root, "file_id"); let path, path_ok = string_field(root, "path");
            let start_line, sl_ok = int_field(root, "start_line"); let end_line, el_ok = int_field(root, "end_line");
            let precision, precision_ok = string_field(root, "precision");
            let start_byte_node = json::member(root, "start_byte"); let end_byte_node = json::member(root, "end_byte");
            let start_column_node = json::member(root, "start_column"); let end_column_node = json::member(root, "end_column");
            let callee_node = json::member(root, "callee_id"); let builtin_node = json::member(root, "builtin_id");
            let arity, arity_ok = int_field(root, "result_arity"); let arg_count, arg_count_ok = int_field(root, "arg_count");
            let use_shape, shape_ok = string_field(root, "use_shape");
            var callee = keep(""); var builtin = keep("");
            var callee_ok = is_null(callee_node); var builtin_ok = is_null(builtin_node);
            if !callee_ok { let value, ok = json::as_string(callee_node); callee = keep(value); callee_ok = ok; }
            if !builtin_ok { let value, ok = json::as_string(builtin_node); builtin = keep(value); builtin_ok = ok; }
            if !id_ok || id != call_facts.len || !sid_ok ||
               (is_null(specialization_node) && specialization_id != -1) ||
               (!is_null(specialization_node) && (specialization_id < 0 || specialization_id >= specialization_facts.len)) ||
               !fid_ok || file_id < 0 || file_id >= source_facts.len || !path_ok || path != source_facts[file_id].path ||
               !sl_ok || !el_ok || start_line < 1 || end_line < start_line || !precision_ok || !callee_ok || !builtin_ok ||
               !arity_ok || arity < 0 || !arg_count_ok || arg_count < 0 || arg_count > MAX_RECORDS || !shape_ok ||
               (use_shape != "statement" && use_shape != "tuple_binding" && use_shape != "scalar" && use_shape != "return" && use_shape != "unknown") {
                error.append("call fact has invalid fields"); return false;
            }
            var start_byte = 0; var end_byte = 0; var start_column = 0; var end_column = 0;
            if precision == "exact" {
                let sb, sb_ok = json::as_i64(start_byte_node); let eb, eb_ok = json::as_i64(end_byte_node);
                let sc, sc_ok = json::as_i64(start_column_node); let ec, ec_ok = json::as_i64(end_column_node);
                if !sb_ok || !eb_ok || !sc_ok || !ec_ok || sb < 0 || eb < sb || eb > source_facts[file_id].byte_length || sc < 1 || ec < 1 {
                    error.append("exact call location is invalid"); return false;
                }
                start_byte = sb; end_byte = eb; start_column = sc; end_column = ec;
            } else if precision == "line" {
                if !is_null(start_byte_node) || !is_null(end_byte_node) || !is_null(start_column_node) || !is_null(end_column_node) {
                    error.append("line call location contains fabricated precision"); return false;
                }
            } else { error.append("call location precision is invalid"); return false; }
            if have_previous_call {
                let out_of_order = specialization_id < previous_call_specialization ||
                    (specialization_id == previous_call_specialization && bytewise_less(path, previous_call_path)) ||
                    (specialization_id == previous_call_specialization && path == previous_call_path && start_byte < previous_call_start) ||
                    (specialization_id == previous_call_specialization && path == previous_call_path && start_byte == previous_call_start && bytewise_less(use_shape, previous_call_use));
                if out_of_order { error.append("call facts are not deterministically sorted"); return false; }
            }
            previous_call_specialization = specialization_id; previous_call_path = keep(path);
            previous_call_start = start_byte; previous_call_use = keep(use_shape); have_previous_call = true;
            call_facts.push(CallFact { id: id, specialization_id: specialization_id, file_id: file_id, path: keep(path),
                start_byte: start_byte, end_byte: end_byte, start_line: start_line, end_line: end_line,
                start_column: start_column, end_column: end_column, precision: keep(precision),
                callee_id: keep(callee), builtin_id: keep(builtin), result_arity: arity,
                arg_count: arg_count, use_shape: keep(use_shape) });
            call_argument_counts.push(0);
            hash = hash_line(hash, line);
        } else if kind == "result_use" {
            if phase < 5 || phase > 7 { error.append("result_use fact is out of order"); return false; }
            phase = 7;
            let call_id, call_ok = int_field(root, "call_id"); let result_index, index_ok = int_field(root, "result_index");
            let state, state_ok = string_field(root, "state"); let binding_node = json::member(root, "binding_name");
            let referenced_node = json::member(root, "referenced");
            var binding = keep(""); var binding_ok = is_null(binding_node);
            var referenced = false; var referenced_known = is_null(referenced_node);
            if !binding_ok { let value, ok = json::as_string(binding_node); binding = keep(value); binding_ok = ok; }
            if !referenced_known { let value, ok = json::as_bool(referenced_node); referenced = value; referenced_known = ok; }
            if !call_ok || call_id < 0 || call_id >= call_facts.len || !index_ok || result_index < 0 ||
               result_index >= call_facts[call_id].result_arity || !state_ok ||
               (state != "discarded" && state != "bound" && state != "overwritten" && state != "returned" && state != "unknown") ||
               !binding_ok || !referenced_known || (state == "bound" && (binding.len == 0 || is_null(referenced_node))) ||
               (state == "overwritten" && (binding.len == 0 || is_null(referenced_node))) ||
               ((state != "bound" && state != "overwritten") && (!is_null(binding_node) || !is_null(referenced_node))) {
                error.append("result_use fact has invalid fields"); return false;
            }
            if have_previous_result && (call_id < previous_result_call || (call_id == previous_result_call && result_index < previous_result_index)) {
                error.append("result_use facts are not deterministically sorted"); return false;
            }
            previous_result_call = call_id; previous_result_index = result_index; have_previous_result = true;
            result_use_facts.push(ResultUseFact { call_id: call_id, result_index: result_index, state: keep(state),
                binding_name: keep(binding), referenced: referenced });
            hash = hash_line(hash, line);
        } else if kind == "call_argument" {
            if phase < 5 || phase > 8 { error.append("call_argument fact is out of order"); return false; }
            phase = 8;
            let call_id, call_ok = int_field(root, "call_id"); let index, index_ok = int_field(root, "index");
            let shape, shape_ok = string_field(root, "shape");
            let variable_node = json::member(root, "variable_id"); let nested_node = json::member(root, "nested_call_id");
            var variable_id = keep(""); var variable_ok = is_null(variable_node);
            var nested_call_id = -1; var nested_ok = is_null(nested_node);
            if !variable_ok { let value, ok = json::as_string(variable_node); variable_id = keep(value); variable_ok = ok; }
            if !nested_ok { let value, ok = json::as_i64(nested_node); nested_call_id = value; nested_ok = ok; }
            if !call_ok || call_id < 0 || call_id >= call_facts.len || !index_ok || index < 0 ||
               index >= call_facts[call_id].arg_count || index != call_argument_counts[call_id] || !shape_ok ||
               (shape != "identifier" && shape != "slice" && shape != "call" && shape != "other") ||
               !variable_ok || !nested_ok ||
               ((shape == "identifier" || shape == "slice") && (variable_id.len == 0 || !is_null(nested_node))) ||
               (shape == "call" && (!is_null(variable_node) || nested_call_id < 0 || nested_call_id >= call_facts.len)) ||
               (shape == "other" && (!is_null(variable_node) || !is_null(nested_node))) {
                error.append("call_argument fact has invalid fields"); return false;
            }
            call_argument_facts.push(CallArgumentFact { call_id: call_id, index: index, shape: keep(shape),
                variable_id: keep(variable_id), nested_call_id: nested_call_id });
            call_argument_counts[call_id]++;
            hash = hash_line(hash, line);
        } else if kind == "pure_value" {
            if phase < 5 || phase > 9 { error.append("pure_value facts are out of order"); return false; }
            phase = 9;
            let id, id_ok = int_field(root, "id"); let specialization_id, sid_ok = int_field(root, "specialization_id");
            let file_id, fid_ok = int_field(root, "file_id"); let path, path_ok = string_field(root, "path");
            let start_byte, sb_ok = int_field(root, "start_byte"); let end_byte, eb_ok = int_field(root, "end_byte");
            let start_line, sl_ok = int_field(root, "start_line"); let end_line, el_ok = int_field(root, "end_line");
            let expression_kind, expression_ok = string_field(root, "expression_kind"); let proof, proof_ok = string_field(root, "proof");
            if !id_ok || id != expected_pure_value || !sid_ok || specialization_id < 0 || specialization_id >= specialization_facts.len ||
               !fid_ok || file_id < 0 || file_id >= source_facts.len || !path_ok || path != source_facts[file_id].path ||
               !sb_ok || !eb_ok || start_byte < 0 || end_byte < start_byte || end_byte > source_facts[file_id].byte_length ||
               !sl_ok || !el_ok || start_line < 1 || end_line < start_line || !expression_ok ||
               (expression_kind != "integer_literal" && expression_kind != "float_literal" &&
                expression_kind != "boolean_literal" && expression_kind != "string_literal" &&
                expression_kind != "constant_integer_expression" && expression_kind != "floating_expression" &&
                expression_kind != "boolean_expression" && expression_kind != "pure_expression") ||
               !proof_ok || proof != "typed-subtree-effect-free-and-nontrapping" {
                error.append("pure_value fact has invalid fields"); return false;
            }
            if have_previous_pure && (file_id < previous_pure_file ||
               (file_id == previous_pure_file && start_byte < previous_pure_start) ||
               (file_id == previous_pure_file && start_byte == previous_pure_start && specialization_id < previous_pure_specialization)) {
                error.append("pure_value facts are not deterministically sorted"); return false;
            }
            previous_pure_file = file_id; previous_pure_start = start_byte;
            previous_pure_specialization = specialization_id; have_previous_pure = true;
            pure_value_facts.push(PureValueFact { id: id, specialization_id: specialization_id, file_id: file_id,
                path: keep(path), start_byte: start_byte, end_byte: end_byte, start_line: start_line,
                end_line: end_line, expression_kind: keep(expression_kind), proof: keep(proof) });
            expected_pure_value++;
            hash = hash_line(hash, line);
        } else if kind == "overflow_guard" {
            if phase < 5 || phase > 10 { error.append("overflow_guard fact is out of order"); return false; }
            phase = 10;
            let id, id_ok = int_field(root, "id"); let specialization_id, sid_ok = int_field(root, "specialization_id");
            let file_id, fid_ok = int_field(root, "file_id"); let path, path_ok = string_field(root, "path");
            let operation, operation_ok = string_field(root, "operation"); let signed, signed_ok = bool_field(root, "signed");
            let width, width_ok = int_field(root, "width"); let nonnegative, nonnegative_ok = bool_field(root, "right_nonnegative");
            let result_matches, result_ok = bool_field(root, "result_matches"); let source_matches, source_ok = bool_field(root, "source_matches");
            let relation, relation_ok = string_field(root, "relation");
            let result_name, result_name_ok = string_field(root, "result_name"); let source_name, source_name_ok = string_field(root, "source_name");
            let arithmetic_start, arithmetic_start_ok = int_field(root, "arithmetic_start_byte");
            let arithmetic_end, arithmetic_end_ok = int_field(root, "arithmetic_end_byte");
            let arithmetic_line, arithmetic_line_ok = int_field(root, "arithmetic_start_line");
            let arithmetic_end_line, arithmetic_end_line_ok = int_field(root, "arithmetic_end_line");
            let arithmetic_start_column, arithmetic_start_column_ok = int_field(root, "arithmetic_start_column");
            let arithmetic_end_column, arithmetic_end_column_ok = int_field(root, "arithmetic_end_column");
            let guard_start, guard_start_ok = int_field(root, "guard_start_byte");
            let guard_end, guard_end_ok = int_field(root, "guard_end_byte");
            let guard_line, guard_line_ok = int_field(root, "guard_start_line");
            let guard_end_line, guard_end_line_ok = int_field(root, "guard_end_line");
            let guard_start_column, guard_start_column_ok = int_field(root, "guard_start_column");
            let guard_end_column, guard_end_column_ok = int_field(root, "guard_end_column");
            if !object_count(root, 26) || !id_ok || id != overflow_guard_facts.len || !sid_ok || specialization_id < 0 || specialization_id >= specialization_facts.len ||
               !fid_ok || file_id < 0 || file_id >= source_facts.len || !path_ok || path != source_facts[file_id].path ||
               !operation_ok || (operation != "add" && operation != "subtract") || !signed_ok || !width_ok ||
               (width != 8 && width != 16 && width != 32 && width != 64) || !nonnegative_ok || !result_ok || !source_ok ||
               !relation_ok || (relation != "lt" && relation != "gt") || !result_name_ok || result_name.len == 0 ||
               !source_name_ok || source_name.len == 0 || !arithmetic_start_ok || !arithmetic_end_ok ||
               arithmetic_start < 0 || arithmetic_end <= arithmetic_start || arithmetic_end > source_facts[file_id].byte_length ||
               !arithmetic_line_ok || arithmetic_line < 1 || !arithmetic_end_line_ok || arithmetic_end_line < arithmetic_line ||
               !arithmetic_start_column_ok || arithmetic_start_column < 1 ||
               !arithmetic_end_column_ok || arithmetic_end_column < 1 ||
               !guard_start_ok || !guard_end_ok || guard_start < 0 || guard_end <= guard_start ||
               guard_end > source_facts[file_id].byte_length || !guard_line_ok || guard_line < 1 ||
               !guard_end_line_ok || guard_end_line < guard_line ||
               !guard_start_column_ok || guard_start_column < 1 ||
               !guard_end_column_ok || guard_end_column < 1 {
                error.append("overflow_guard fact has invalid fields"); return false;
            }
            overflow_guard_facts.push(OverflowGuardFact { id: id, specialization_id: specialization_id, file_id: file_id,
                path: keep(path), operation: keep(operation), signed: signed, width: width,
                right_nonnegative: nonnegative, result_matches: result_matches, source_matches: source_matches,
                relation: keep(relation), result_name: keep(result_name), source_name: keep(source_name),
                arithmetic_start: arithmetic_start, arithmetic_end: arithmetic_end, arithmetic_line: arithmetic_line,
                arithmetic_end_line: arithmetic_end_line, arithmetic_start_column: arithmetic_start_column,
                arithmetic_end_column: arithmetic_end_column, guard_start: guard_start, guard_end: guard_end,
                guard_line: guard_line, guard_end_line: guard_end_line,
                guard_start_column: guard_start_column, guard_end_column: guard_end_column });
            hash = hash_line(hash, line);
        } else if kind == "slice_length" {
            if phase < 5 || phase > 11 { error.append("slice_length fact is out of order"); return false; }
            phase = 11;
            let id, id_ok = int_field(root, "id"); let specialization_id, sid_ok = int_field(root, "specialization_id");
            let file_id, fid_ok = int_field(root, "file_id"); let path, path_ok = string_field(root, "path");
            let view_name, view_ok = string_field(root, "view_name"); let root_name, root_ok = string_field(root, "root_name");
            let capture_before, capture_order_ok = bool_field(root, "capture_before_growth");
            let growth_before, growth_order_ok = bool_field(root, "growth_before_use");
            let same_root, same_root_ok = bool_field(root, "same_root"); let current_length, current_length_ok = bool_field(root, "index_uses_current_length");
            let capture_start, capture_start_ok = int_field(root, "capture_start_byte");
            let capture_end, capture_end_ok = int_field(root, "capture_end_byte"); let capture_line, capture_line_ok = int_field(root, "capture_start_line");
            let capture_start_column, capture_start_column_ok = int_field(root, "capture_start_column");
            let capture_end_column, capture_end_column_ok = int_field(root, "capture_end_column");
            let growth_start, growth_start_ok = int_field(root, "growth_start_byte"); let growth_end, growth_end_ok = int_field(root, "growth_end_byte");
            let growth_line, growth_line_ok = int_field(root, "growth_start_line");
            let growth_start_column, growth_start_column_ok = int_field(root, "growth_start_column");
            let growth_end_column, growth_end_column_ok = int_field(root, "growth_end_column");
            let use_start, use_start_ok = int_field(root, "use_start_byte"); let use_end, use_end_ok = int_field(root, "use_end_byte");
            let use_line, use_line_ok = int_field(root, "use_start_line"); let use_end_line, use_end_line_ok = int_field(root, "use_end_line");
            let use_start_column, use_start_column_ok = int_field(root, "use_start_column");
            let use_end_column, use_end_column_ok = int_field(root, "use_end_column");
            if !object_count(root, 27) || !id_ok || id != slice_length_facts.len || !sid_ok || specialization_id < 0 || specialization_id >= specialization_facts.len ||
               !fid_ok || file_id < 0 || file_id >= source_facts.len || !path_ok || path != source_facts[file_id].path ||
               !view_ok || view_name.len == 0 || !root_ok || root_name.len == 0 || !capture_order_ok || !growth_order_ok ||
               !same_root_ok || !current_length_ok || !capture_before || !growth_before || !same_root || !current_length ||
               !capture_start_ok || !capture_end_ok || capture_start < 0 || capture_end <= capture_start || capture_end > source_facts[file_id].byte_length ||
               !capture_line_ok || capture_line < 1 || !growth_start_ok || !growth_end_ok || growth_start < 0 || growth_end <= growth_start || growth_end > source_facts[file_id].byte_length ||
               !capture_start_column_ok || capture_start_column < 1 || !capture_end_column_ok || capture_end_column < 1 ||
               !growth_line_ok || growth_line < 1 || !growth_start_column_ok || growth_start_column < 1 || !growth_end_column_ok || growth_end_column < 1 ||
               !use_start_ok || !use_end_ok || use_start < 0 || use_end <= use_start || use_end > source_facts[file_id].byte_length ||
               !use_line_ok || use_line < 1 || !use_end_line_ok || use_end_line < use_line ||
               !use_start_column_ok || use_start_column < 1 || !use_end_column_ok || use_end_column < 1 {
                error.append("slice_length fact has invalid fields"); return false;
            }
            slice_length_facts.push(SliceLengthFact { id: id, specialization_id: specialization_id, file_id: file_id,
                path: keep(path), view_name: keep(view_name), root_name: keep(root_name),
                capture_before_growth: capture_before, growth_before_use: growth_before, same_root: same_root,
                index_uses_current_length: current_length, capture_start: capture_start, capture_end: capture_end,
                capture_line: capture_line, capture_start_column: capture_start_column, capture_end_column: capture_end_column,
                growth_start: growth_start, growth_end: growth_end, growth_line: growth_line,
                growth_start_column: growth_start_column, growth_end_column: growth_end_column,
                use_start: use_start, use_end: use_end, use_line: use_line, use_end_line: use_end_line,
                use_start_column: use_start_column, use_end_column: use_end_column });
            hash = hash_line(hash, line);
        } else if kind == "coverage" {
            if phase < 1 || phase > 12 { error.append("coverage fact is out of order"); return false; }
            phase = 12;
            let id, id_ok = int_field(root, "file_id"); let path, path_ok = string_field(root, "path");
            let parse, parse_ok = string_field(root, "parse"); let semantic, semantic_ok = string_field(root, "semantic");
            let checked, checked_ok = int_field(root, "checked_specializations");
            let unchecked, unchecked_ok = int_field(root, "unchecked_generics");
            let unsupported = json::member(root, "unsupported");
            if !object_count(root, 8) || !id_ok || id != expected_coverage || id < 0 || id >= source_facts.len ||
               !path_ok || path != source_facts[id].path || !parse_ok || parse != "complete" ||
               !semantic_ok || semantic != "entry-reachable-specializations" || !checked_ok || checked < 0 ||
               !unchecked_ok || unchecked < 0 { error.append("coverage fact has invalid fields"); return false; }
            var proven_specializations = 0;
            for spec in specialization_facts {
                if spec.file_id == id && spec.reachable_known && spec.reachable { proven_specializations++; }
            }
            if checked != proven_specializations { error.append("coverage checked_specializations disagrees with proven reachable facts"); return false; }
            guard unsupported else { error.append("coverage unsupported is missing"); return false; }
            match unsupported.val { Arr => {}, _ => { error.append("coverage unsupported is not an array"); return false; } }
            let unsupported_start = analysis_facts.len;
            json::each(unsupported) { item =>
                let name, ok = json::as_string(item);
                if !ok || name.len == 0 { error.append("coverage contains an invalid unsupported analysis"); return false from parse_facts; }
                for prior in analysis_facts[unsupported_start..] { if prior == name { error.append("coverage contains a duplicate unsupported analysis"); return false from parse_facts; } }
                analysis_facts.push(keep(name));
            };
            coverage_facts.push(CoverageFact { file_id: id, path: keep(path), checked: checked, unchecked: unchecked,
                unsupported_start: unsupported_start, unsupported_count: analysis_facts.len - unsupported_start });
            expected_coverage++;
            hash = hash_line(hash, line);
        } else if kind == "end" {
            if phase < 1 || expected_source == 0 || expected_coverage != expected_source ||
               (phase > 12) { error.append("facts end appears before all source coverage"); return false; }
            let count, count_ok = int_field(root, "record_count");
            let integrity, integrity_ok = string_field(root, "integrity");
            if !count_ok || count != records - 1 || !integrity_ok || integrity != hash_text(hash) {
                error.append("facts record count or integrity hash does not match"); return false;
            }
            saw_end = true;
            if offset != input.len { error.append("facts end record is not final"); return false; }
        }
    }
    if !saw_end { error.append("facts stream has no terminal end record"); return false; }
    for call, id in call_facts {
        if call_argument_counts[id] != call.arg_count {
            error.append("call argument facts do not cover every argument"); return false;
        }
    }
    return true;
}

fn append_location(out: u8[>..]&, path: const u8[:], start_byte: i64, end_byte: i64,
                   start_line: i64, start_column: i64, end_line: i64, end_column: i64,
                   precision: const u8[:]) {
    out.append("{\"path\":"); json::format_string(out, path);
    if precision == "exact" {
        format(out, ",\"start_byte\":", start_byte, ",\"end_byte\":", end_byte,
               ",\"start_line\":", start_line, ",\"start_column\":", start_column,
               ",\"end_line\":", end_line, ",\"end_column\":", end_column,
               ",\"precision\":\"exact\"}");
    } else {
        format(out, ",\"start_byte\":null,\"end_byte\":null,\"start_line\":", start_line,
               ",\"start_column\":null,\"end_line\":null,\"end_column\":null,\"precision\":\"line\"}");
    }
}

fn rule_selected(code: const u8[:], groups: (const u8[:])[>..]&, enabled: (const u8[:])[>..]&,
                 config_allow: (const u8[:])[>..]&, config_deny: (const u8[:])[>..]&, 
                 cli_allow: (const u8[:])[>..]&, cli_deny: (const u8[:])[>..]&) -> bool {
    var selected = false;
    for group in groups {
        if group == "existing" && (code == "redundant_cast" || code == "redundant_reference_marker" || code == "avoidable_reference_copy") { selected = true; }
        if group == "correctness" && (code == "discarded_failure" || code == "unchecked_poll_result" || code == "stale_suppression") { selected = true; }
        if group == "suspicious" && code == "unused_pure_value" { selected = true; }
        if group == "review" && (code == "post_overflow_guard" || code == "stale_slice_length") { selected = true; }
        if group == "performance" && code == "specialization_fanout" { selected = true; }
        if group == "project" && (code == "view_before_append_argument" || code == "foreign_container_index") { selected = true; }
    }
    if contains_value(enabled, code) { selected = true; }
    if contains_value(config_deny, code) { selected = true; }
    if contains_value(config_allow, code) { selected = false; }
    if contains_value(cli_allow, code) { selected = false; }
    if contains_value(cli_deny, code) { selected = true; }
    return selected;
}

fn rule_denied(code: const u8[:], config_allow: (const u8[:])[>..]&, config_deny: (const u8[:])[>..]&, 
               cli_allow: (const u8[:])[>..]&, cli_deny: (const u8[:])[>..]&,
               severities: SeverityOverride[>..]&) -> bool {
    if contains_value(cli_deny, code) { return true; }
    if contains_value(cli_allow, code) { return false; }
    if contains_value(config_allow, code) { return false; }
    if contains_value(config_deny, code) { return true; }
    return severity_for(code, severities) == "error";
}

fn append_unsupported(out: u8[>..]&, coverage: CoverageFact&) {
    var first = true;
    // The producer's exact list is retained, then the unimplemented required
    // analyses are disclosed even when they do not yet have dedicated facts.
    for i in coverage.unsupported_start..coverage.unsupported_start + coverage.unsupported_count {
        let name = analysis_facts[i];
        if analysis_supported(name) { continue; }
        if !first { out.push(','); } first = false;
        out.append("{\"analysis\":"); json::format_string(out, name);
        out.append(",\"reason\":\"required semantic facts are not available\"}");
    }
    let missing = ["unused_pure_value", "stale_suppression", "post_overflow_guard", "stale_slice_length", "specialization_fanout",
                   "view_before_append_argument", "foreign_container_index"];
    for name in missing {
        var present = false;
        for i in coverage.unsupported_start..coverage.unsupported_start + coverage.unsupported_count {
            if analysis_facts[i] == name { present = true; }
        }
        if !present && !analysis_supported(name) {
            if !first { out.push(','); } first = false;
            out.append("{\"analysis\":"); json::format_string(out, name);
            out.append(",\"reason\":\"required semantic facts are not available\"}");
        }
    }
    if project_contracts_required && contract_apis.len == 0 {
        for name in ["view_before_append_argument", "foreign_container_index"] {
            if rule_selected(name, groups, enabled, config_allow, config_deny, allow, deny) {
                if !first { out.push(','); } first = false;
                out.append("{\"analysis\":"); json::format_string(out, name);
                out.append(",\"reason\":\"selected project rule requires a contracts file\"}");
            }
        }
    }
}

fn analysis_supported(name: const u8[:]) -> bool {
    if name == "discarded_failure" || name == "unchecked_poll_result" ||
       name == "stale_suppression" || name == "unused_pure_value" ||
       name == "post_overflow_guard" || name == "stale_slice_length" ||
       name == "view_before_append_argument" || name == "foreign_container_index" { return true; }
    if name == "specialization_fanout" {
        for coverage in coverage_facts {
            for i in coverage.unsupported_start..coverage.unsupported_start + coverage.unsupported_count {
                if analysis_facts[i] == "specialization_reachability" || analysis_facts[i] == "specialization_fanout" { return false; }
            }
        }
        for spec in specialization_facts { if !spec.reachable_known { return false; } }
        return true;
    }
    return false;
}

fn diagnostic_group(code: const u8[:]) -> const u8[:] {
    if code == "redundant_cast" || code == "redundant_reference_marker" || code == "avoidable_reference_copy" { return "existing"; }
    if code == "specialization_fanout" { return "performance"; }
    if code == "unused_pure_value" { return "suspicious"; }
    if code == "post_overflow_guard" || code == "stale_slice_length" { return "review"; }
    if code == "view_before_append_argument" || code == "foreign_container_index" { return "project"; }
    return "correctness";
}

fn make_diagnostic(code: const u8[:], message: const u8[:], file_id: i64,
                   start_byte: i64, end_byte: i64, start_line: i64, start_column: i64,
                   end_line: i64, end_column: i64, precision: const u8[:],
                   evidence_json: const u8[:], specialization_json: const u8[:]) -> OutputDiagnostic {
    return OutputDiagnostic { code: keep(code), message: keep(message), file_id: file_id, group: diagnostic_group(code),
        severity: "warning", confidence: "high", start_byte: start_byte, end_byte: end_byte,
        start_line: start_line, start_column: start_column, end_line: end_line, end_column: end_column,
        precision: keep(precision), suppressed: false, suppression_reason: "", suppression_file_id: -1,
        suppression_start: 0, suppression_end: 0, suppression_line: 0,
        evidence_json: keep(evidence_json), specialization_json: keep(specialization_json),
        baseline_fingerprint: "", baseline_occurrence: 0, baselined: false };
}

fn severity_for(code: const u8[:], overrides: SeverityOverride[>..]&) -> const u8[:] {
    for override in overrides { if override.code == code { return override.severity; } }
    return "warning";
}

fn call_specializations_json(call: CallFact&) -> const u8[:] {
    var out: u8[>..] = [];
    out.push('[');
    if call.specialization_id >= 0 {
        let spec = specialization_facts[call.specialization_id];
        var text: u8[>..] = [];
        format(text, spec.name, " (", spec.context, ")");
        json::format_string(out, text);
    }
    out.push(']');
    return keep(out);
}

fn status_evidence(identity: const u8[:], result_index: i64, state: const u8[:], binding: const u8[:]) -> const u8[:] {
    var out: u8[>..] = [];
    out.append("{\"callee\":"); json::format_string(out, identity);
    format(out, ",\"status_result\":", result_index, ",\"use\":");
    json::format_string(out, if state == "bound" { "bound_but_unreferenced" } else { state });
    if binding.len > 0 { out.append(",\"binding\":"); json::format_string(out, binding); }
    out.push('}');
    return keep(out);
}

fn failure_message(is_parse: bool, discarded: bool, overwritten: bool, binding: const u8[:]) -> const u8[:] {
    var out: u8[>..] = [];
    let name = if is_parse { "stdlib::parse_int" } else { "qpoll" };
    if discarded { format(out, name, " status result is discarded"); }
    else if overwritten { format(out, name, " status binding ", binding, " is overwritten before inspection"); }
    else { format(out, name, " status binding ", binding, " is never referenced"); }
    return keep(out);
}

fn pure_value_message(expression_kind: const u8[:]) -> const u8[:] {
    var out: u8[>..] = []; format(out, "discarded ", expression_kind, " has no observable effect");
    return keep(out);
}

fn overflow_guard_message(width: i64, operation: const u8[:]) -> const u8[:] {
    var out: u8[>..] = [];
    format(out, "signed i", width, " ", operation,
           " is checked after evaluation; debug builds trap before this guard and release builds wrap");
    return keep(out);
}

fn specialization_context_json(id: i64) -> const u8[:] {
    var out: u8[>..] = [];
    out.push('[');
    if id >= 0 && id < specialization_facts.len {
        let spec = specialization_facts[id];
        var context: u8[>..] = []; format(context, spec.name, " (", spec.context, ")");
        json::format_string(out, context);
    }
    out.push(']');
    return keep(out);
}

fn fanout_message(name: const u8[:], unknown_count: i64, reachable_count: i64) -> const u8[:] {
    var out: u8[>..] = [];
    format(out, "function ", name, " has ", if unknown_count > 0 { "at least " } else { "" }, reachable_count, " reachable specializations");
    return keep(out);
}

fn view_before_append_message(callee: const u8[:]) -> const u8[:] {
    var out: u8[>..] = [];
    format(out, "call to ", callee,
           " captures a view before a later argument grows the same owner, then uses the view after growth");
    return keep(out);
}

fn foreign_index_message(callee: const u8[:]) -> const u8[:] {
    var out: u8[>..] = [];
    format(out, "call to ", callee,
           " consumes an index produced for a different container owner");
    return keep(out);
}

fn build_candidates() {
    candidate_facts.clear();
    for warning in warning_facts {
        candidate_facts.push(make_diagnostic(warning.code, warning.message, warning.file_id,
            warning.start_byte, warning.end_byte, warning.start_line, warning.start_column,
            warning.end_line, warning.end_column, warning.precision, "null", warning.specialization_json));
    }
    for use in result_use_facts {
        let call = call_facts[use.call_id];
        let is_parse = call.callee_id == "stdlib::parse_int";
        let is_poll = call.builtin_id == "goose::builtin::qpoll";
        if (!is_parse && !is_poll) || call.result_arity < 2 || use.result_index != call.result_arity - 1 { continue; }
        let discarded = use.state == "discarded";
        let unused_binding = (use.state == "bound" || use.state == "overwritten") && !use.referenced;
        if !discarded && !unused_binding { continue; }
        let code = if is_parse { "discarded_failure" } else { "unchecked_poll_result" };
        let message = failure_message(is_parse, discarded, use.state == "overwritten", use.binding_name);
        let identity = if is_parse { "stdlib::parse_int" } else { "goose::builtin::qpoll" };
        let evidence = status_evidence(identity, use.result_index, use.state, use.binding_name);
        let context = call_specializations_json(call);
        candidate_facts.push(make_diagnostic(code, message, call.file_id, call.start_byte, call.end_byte,
            call.start_line, call.start_column, call.end_line, call.end_column, call.precision, evidence, context));
    }

    var pure_index = 0;
    while pure_index < pure_value_facts.len {
        let pure = pure_value_facts[pure_index];
        var end = pure_index + 1;
        var contexts: u8[>..] = [];
        contexts.push('[');
        var context_first = true;
        var last_specialization = -1;
        while end < pure_value_facts.len && pure_value_facts[end].file_id == pure.file_id &&
              pure_value_facts[end].start_byte == pure.start_byte && pure_value_facts[end].end_byte == pure.end_byte {
            end++;
        }
        for j in pure_index..end {
            let fact = pure_value_facts[j];
            if fact.specialization_id == last_specialization { continue; }
            last_specialization = fact.specialization_id;
            let spec = specialization_facts[fact.specialization_id];
            var context: u8[>..] = []; format(context, spec.name, " (", spec.context, ")");
            if !context_first { contexts.push(','); } context_first = false;
            json::format_string(contexts, context);
        }
        contexts.push(']');
        var evidence: u8[>..] = [];
        evidence.append("{\"expression_kind\":"); json::format_string(evidence, pure.expression_kind);
        evidence.append(",\"proof\":"); json::format_string(evidence, pure.proof); evidence.push('}');
        let message = pure_value_message(pure.expression_kind);
        candidate_facts.push(make_diagnostic("unused_pure_value", message, pure.file_id, pure.start_byte, pure.end_byte,
            pure.start_line, 0, pure.end_line, 0, "exact", evidence, contexts));
        pure_index = end;
    }

    for fact in overflow_guard_facts {
        let canonical_relation =
            (fact.operation == "add" && fact.relation == "lt") ||
            (fact.operation == "subtract" && fact.relation == "gt");
        if !fact.signed || !fact.right_nonnegative || !fact.result_matches ||
           !fact.source_matches || !canonical_relation { continue; }
        var evidence: u8[>..] = [];
        evidence.append("{\"operation\":"); json::format_string(evidence, fact.operation);
        format(evidence, ",\"signed_width\":", fact.width, ",\"result\":");
        json::format_string(evidence, fact.result_name);
        evidence.append(",\"compared_operand\":"); json::format_string(evidence, fact.source_name);
        evidence.append(",\"condition\":"); json::format_string(evidence, fact.relation);
        evidence.append(",\"nonnegative_operand_proof\":\"typed nonnegative value\",\"debug_behavior\":\"overflow traps before the condition\",\"release_behavior\":\"signed operation wraps before the condition\",\"attempted_guard\":{\"path\":");
        json::format_string(evidence, fact.path);
        format(evidence, ",\"start_byte\":", fact.guard_start, ",\"end_byte\":", fact.guard_end,
               ",\"start_line\":", fact.guard_line, ",\"start_column\":", fact.guard_start_column,
               ",\"end_line\":", fact.guard_end_line, ",\"end_column\":", fact.guard_end_column, "}}");
        var diagnostic = make_diagnostic("post_overflow_guard", overflow_guard_message(fact.width, fact.operation),
            fact.file_id, fact.arithmetic_start, fact.arithmetic_end, fact.arithmetic_line, fact.arithmetic_start_column,
            fact.arithmetic_end_line, fact.arithmetic_end_column, "exact", evidence, specialization_context_json(fact.specialization_id));
        diagnostic.confidence = "medium";
        candidate_facts.push(diagnostic);
    }

    for fact in slice_length_facts {
        if !fact.capture_before_growth || !fact.growth_before_use || !fact.same_root ||
           !fact.index_uses_current_length { continue; }
        var message: u8[>..] = [];
        format(message, "slice ", fact.view_name, " keeps its earlier length after ", fact.root_name,
               " grows, but the later index uses the array's current last element");
        var evidence: u8[>..] = [];
        evidence.append("{\"view\":"); json::format_string(evidence, fact.view_name);
        evidence.append(",\"array\":"); json::format_string(evidence, fact.root_name);
        evidence.append(",\"same_root\":true,\"captured_length_is_fixed\":true,\"index\":\"array.len - 1\",\"capture\":{\"path\":");
        json::format_string(evidence, fact.path);
        format(evidence, ",\"start_byte\":", fact.capture_start, ",\"end_byte\":", fact.capture_end,
               ",\"start_line\":", fact.capture_line, ",\"start_column\":", fact.capture_start_column,
               ",\"end_column\":", fact.capture_end_column, "},\"growth\":{\"path\":");
        json::format_string(evidence, fact.path);
        format(evidence, ",\"start_byte\":", fact.growth_start, ",\"end_byte\":", fact.growth_end,
               ",\"start_line\":", fact.growth_line, ",\"start_column\":", fact.growth_start_column,
               ",\"end_column\":", fact.growth_end_column, "},\"use\":{\"path\":");
        json::format_string(evidence, fact.path);
        format(evidence, ",\"start_byte\":", fact.use_start, ",\"end_byte\":", fact.use_end,
               ",\"start_line\":", fact.use_line, ",\"start_column\":", fact.use_start_column,
               ",\"end_line\":", fact.use_end_line, ",\"end_column\":", fact.use_end_column, "}}");
        candidate_facts.push(make_diagnostic("stale_slice_length", message, fact.file_id,
            fact.use_start, fact.use_end, fact.use_line, fact.use_start_column,
            fact.use_end_line, fact.use_end_column,
            "exact", evidence, specialization_context_json(fact.specialization_id)));
    }

    for outer, outer_id in call_facts {
        let identity = resolved_call_name(outer);
        let view_api_id = contract_api_index(identity, "view_after_append");
        if view_api_id >= 0 {
            let api = contract_apis[view_api_id];
            let view_arg = api.view_arg; let append_arg = api.append_arg;
            let nested_id = argument_nested_call(outer_id, append_arg);
            let view_owner = argument_variable(outer_id, view_arg);
            if view_arg < append_arg && argument_shape(outer_id, view_arg) == "slice" &&
               argument_shape(outer_id, append_arg) == "call" && nested_id >= 0 &&
               view_owner.len > 0 && nested_id < call_facts.len {
                let append_call = call_facts[nested_id];
                let append_api_id = contract_api_index(resolved_call_name(append_call), "append_to");
                if append_api_id >= 0 {
                    let owner_arg = contract_apis[append_api_id].owner_arg;
                    let append_owner = argument_variable(nested_id, owner_arg);
                    if append_call.specialization_id == outer.specialization_id &&
                       append_call.file_id == outer.file_id && append_owner == view_owner {
                        var evidence: u8[>..] = [];
                        evidence.append("{\"callee\":"); json::format_string(evidence, identity);
                        format(evidence, ",\"view_argument\":", view_arg,
                               ",\"append_argument\":", append_arg,
                               ",\"append_callee\":");
                        json::format_string(evidence, resolved_call_name(append_call));
                        evidence.append(",\"same_owner\":true,\"argument_evaluation\":\"left-to-right\",\"view_length\":\"captured before append\",\"contract\":\"callee uses the view after append\"}");
                        candidate_facts.push(make_diagnostic("view_before_append_argument",
                            view_before_append_message(identity), outer.file_id,
                            outer.start_byte, outer.end_byte, outer.start_line, outer.start_column,
                            outer.end_line, outer.end_column, outer.precision, evidence,
                            call_specializations_json(outer)));
                    }
                }
            }
        }

        let consumer_api_id = contract_api_index(identity, "consumes_index");
        if consumer_api_id >= 0 {
            let api = contract_apis[consumer_api_id];
            let nested_id = argument_nested_call(outer_id, api.index_arg);
            let consumer_owner = argument_variable(outer_id, api.owner_arg);
            if argument_shape(outer_id, api.owner_arg) == "identifier" &&
               argument_shape(outer_id, api.index_arg) == "call" && nested_id >= 0 &&
               nested_id < call_facts.len && consumer_owner.len > 0 {
                let producer = call_facts[nested_id];
                let producer_api_id = contract_api_index(resolved_call_name(producer), "index_of");
                if producer_api_id >= 0 {
                    let producer_owner_arg = contract_apis[producer_api_id].owner_arg;
                    let producer_owner = argument_variable(nested_id, producer_owner_arg);
                    if producer.specialization_id == outer.specialization_id &&
                       producer.file_id == outer.file_id && producer_owner.len > 0 &&
                       producer_owner != consumer_owner {
                        var evidence: u8[>..] = [];
                        evidence.append("{\"consumer\":"); json::format_string(evidence, identity);
                        format(evidence, ",\"consumer_owner_argument\":", api.owner_arg,
                               ",\"index_argument\":", api.index_arg,
                               ",\"producer\":");
                        json::format_string(evidence, resolved_call_name(producer));
                        format(evidence, ",\"producer_owner_argument\":", producer_owner_arg);
                        evidence.append(",\"owner_mismatch\":true,\"provenance\":\"exact nested producer call and direct local owners\"}");
                        candidate_facts.push(make_diagnostic("foreign_container_index",
                            foreign_index_message(identity), outer.file_id,
                            outer.start_byte, outer.end_byte, outer.start_line, outer.start_column,
                            outer.end_line, outer.end_column, outer.precision, evidence,
                            call_specializations_json(outer)));
                    }
                }
            }
        }
    }

    var i = 0;
    while i < specialization_facts.len {
        var end = i + 1;
        let first = specialization_facts[i];
        while end < specialization_facts.len && specialization_facts[end].path == first.path &&
              specialization_facts[end].start_line == first.start_line && specialization_facts[end].name == first.name { end++; }
        var reachable_count = 0; var unknown_count = 0;
        for j in i..end {
            if specialization_facts[j].reachable_known && specialization_facts[j].reachable { reachable_count++; }
            else if !specialization_facts[j].reachable_known { unknown_count++; }
        }
        if reachable_count >= 2 {
            var contexts: u8[>..] = [];
            var evidence: u8[>..] = [];
            contexts.push('['); evidence.push('{');
            json::format_key(evidence, "function"); json::format_string(evidence, first.name);
            evidence.append(",\"reachable_specializations\":"); format(evidence, reachable_count, ",\"reachability_unknown\":", unknown_count, "}");
            var context_first = true;
            for j in i..end {
                let spec = specialization_facts[j];
                if !spec.reachable_known || !spec.reachable { continue; }
                if !context_first { contexts.push(','); } context_first = false;
                var context: u8[>..] = []; format(context, spec.name, " (", spec.context, ")");
                json::format_string(contexts, context);
            }
            contexts.push(']');
            let message = fanout_message(first.name, unknown_count, reachable_count);
            candidate_facts.push(make_diagnostic("specialization_fanout", message, first.file_id,
                first.start_byte, first.end_byte, first.start_line, first.start_column,
                first.end_line, first.end_column, first.precision, evidence, contexts));
        }
        i = end;
    }
}

fn output_less(a: OutputDiagnostic&, b: OutputDiagnostic&) -> bool {
    let path_a = if a.file_id < 0 { "<unknown>" } else { source_facts[a.file_id].path };
    let path_b = if b.file_id < 0 { "<unknown>" } else { source_facts[b.file_id].path };
    if path_a != path_b { return bytewise_less(path_a, path_b); }
    if a.start_line != b.start_line { return a.start_line < b.start_line; }
    let start_a = if a.precision == "exact" { a.start_byte } else { -1 };
    let start_b = if b.precision == "exact" { b.start_byte } else { -1 };
    if start_a != start_b { return start_a < start_b; }
    if a.code != b.code { return bytewise_less(a.code, b.code); }
    if a.evidence_json != b.evidence_json { return bytewise_less(a.evidence_json, b.evidence_json); }
    return bytewise_less(a.specialization_json, b.specialization_json);
}

fn coverage_incomplete(coverage: CoverageFact&) -> bool {
    if coverage.unchecked > 0 { return true; }
    for i in coverage.unsupported_start..coverage.unsupported_start + coverage.unsupported_count {
        if !analysis_supported(analysis_facts[i]) { return true; }
    }
    let required = ["unused_pure_value", "stale_suppression", "post_overflow_guard", "stale_slice_length", "specialization_fanout",
                    "view_before_append_argument", "foreign_container_index"];
    for name in required {
        var present = false;
        for i in coverage.unsupported_start..coverage.unsupported_start + coverage.unsupported_count {
            if analysis_facts[i] == name { present = true; }
        }
        if !present && !analysis_supported(name) { return true; }
    }
    if project_contracts_required && contract_apis.len == 0 { return true; }
    return false;
}

fn collect_diagnostics(diagnostics: OutputDiagnostic[>..]&, facts: Facts&, groups: (const u8[:])[>..]&, enabled: (const u8[:])[>..]&, config_allow: (const u8[:])[>..]&, config_deny: (const u8[:])[>..]&, severities: SeverityOverride[>..]&, cli_allow: (const u8[:])[>..]&, cli_deny: (const u8[:])[>..]&) -> i64, i64 {
    build_candidates();
    directive_states.clear();
    for comment in comment_facts {
        var state = directive_state(comment);
        if state.valid {
            for previous in directive_states {
                if previous.valid && previous.code == state.code &&
                   previous.statement_index == state.statement_index {
                    state.valid = false;
                    state.message = "duplicate suppression is unused";
                    break;
                }
            }
        }
        directive_states.push(state);
    }
    diagnostics.clear();
    for candidate in candidate_facts {
        if !rule_selected(candidate.code, groups, enabled, config_allow, config_deny, cli_allow, cli_deny) { continue; }
        var result = make_diagnostic(candidate.code, candidate.message, candidate.file_id,
            candidate.start_byte, candidate.end_byte, candidate.start_line, candidate.start_column,
            candidate.end_line, candidate.end_column, candidate.precision,
            candidate.evidence_json, candidate.specialization_json);
        result.severity = candidate.severity;
        result.confidence = candidate.confidence;
        result.severity = severity_for(result.code, severities);
        let suppression_id = matching_suppression(result);
        if suppression_id >= 0 {
            let state = directive_states[suppression_id];
            let comment = comment_facts[suppression_id];
            result.suppressed = true;
            result.suppression_reason = state.reason;
            result.suppression_file_id = comment.file_id;
            result.suppression_start = comment.start_byte;
            result.suppression_end = comment.end_byte;
            result.suppression_line = comment.line;
        }
        diagnostics.push(result);
    }
    for state, index in directive_states {
        if !state.valid && rule_selected("stale_suppression", groups, enabled,
            config_allow, config_deny, cli_allow, cli_deny) {
            var diagnostic = stale_suppression_diagnostic(comment_facts[index], state);
            diagnostic.severity = severity_for(diagnostic.code, severities);
            diagnostics.push(diagnostic);
        }
    }
    stable_sort(diagnostics) { a, b => output_less(a, b) };
    assign_fingerprints(diagnostics, facts);
    var findings = 0; var suppressed = 0;
    for diagnostic in diagnostics {
        findings++;
        if diagnostic.suppressed { suppressed++; }
    }
    return findings, suppressed;
}

fn append_output_location(out: u8[>..]&, path: const u8[:], start_byte: i64, end_byte: i64,
                          start_line: i64, start_column: i64, end_line: i64, end_column: i64,
                          precision: const u8[:]) {
    out.append("{\"path\":"); json::format_string(out, path);
    if precision == "exact" {
        format(out, ",\"start_byte\":", start_byte, ",\"end_byte\":", end_byte, ",\"start_line\":", start_line,
               ",\"start_column\":"); if start_column > 0 { format(out, start_column); } else { out.append("null"); }
        out.append(",\"end_line\":"); if end_line > 0 { format(out, end_line); } else { out.append("null"); }
        out.append(",\"end_column\":"); if end_column > 0 { format(out, end_column); } else { out.append("null"); }
        out.append(",\"precision\":\"exact\"}");
    } else {
        format(out, ",\"start_byte\":null,\"end_byte\":null,\"start_line\":", start_line,
               ",\"start_column\":null,\"end_line\":null,\"end_column\":null,\"precision\":\"line\"}");
    }
}

fn emit_diagnostic(out: u8[>..]&, diagnostic: OutputDiagnostic&, facts: Facts&) {
    out.append("{\"kind\":\"diagnostic\",\"schema_version\":1,\"code\":"); json::format_string(out, diagnostic.code);
    out.append(",\"group\":"); json::format_string(out, diagnostic.group);
    out.append(",\"severity\":"); json::format_string(out, diagnostic.severity);
    out.append(",\"confidence\":"); json::format_string(out, diagnostic.confidence);
    out.append(",\"message\":"); json::format_string(out, diagnostic.message);
    out.append(",\"primary\":");
    append_output_location(out, source_at(facts, diagnostic.file_id), diagnostic.start_byte, diagnostic.end_byte,
        diagnostic.start_line, diagnostic.start_column, diagnostic.end_line, diagnostic.end_column, diagnostic.precision);
    out.append(",\"related\":[],\"evidence\":"); out.append(diagnostic.evidence_json);
    out.append(",\"specializations\":"); out.append(diagnostic.specialization_json);
    out.append(",\"suppression\":");
    if !diagnostic.suppressed { out.append("null"); }
    else {
        out.append("{\"reason\":"); json::format_string(out, diagnostic.suppression_reason);
        out.append(",\"location\":");
        append_output_location(out, source_at(facts, diagnostic.suppression_file_id), diagnostic.suppression_start,
            diagnostic.suppression_end, diagnostic.suppression_line, 0, diagnostic.suppression_line, 0, "exact");
        out.push('}');
    }
    out.append(",\"baseline\":");
    if !diagnostic.baselined { out.append("null"); }
    else {
        out.append("{\"fingerprint\":"); json::format_string(out, diagnostic.baseline_fingerprint);
        format(out, ",\"occurrence\":", diagnostic.baseline_occurrence, "}");
    }
    out.append(",\"suggestion\":null,\"fixable\":false}\n");
}

// The compiler creates this output path with owner-only permissions; writing it in place preserves that mode.
fn write_lint_output(path: const u8[:], output: u8[>..]&) -> bool {
    return write_file(path, output);
}

fn emit_error(output: const u8[:], format_name: const u8[:], revision: const u8[:], entry: const u8[:],
              profile: const u8[:], code: const u8[:], message: const u8[:], status: i64,
              facts: Facts&, valid: bool) -> i64 {
    var out: u8[>..] = [];
    if format_name == "jsonl" {
        out.append("{\"kind\":\"header\",\"schema_version\":1,\"tool\":\"goose-lint\",\"compiler_revision\":");
        json::format_string(out, revision); out.append(",\"entries\":["); json::format_string(out, entry);
        out.append("],\"profile\":"); json::format_string(out, profile); out.append("}\n");
        if valid {
            for cov in coverage_facts {
                out.append("{\"kind\":\"coverage\",\"schema_version\":1,\"path\":");
                json::format_string(out, cov.path);
                out.append(",\"parse\":\"complete\",\"check\":");
                json::format_string(out, if coverage_incomplete(cov) { "partial" } else { "complete" });
                out.append(",\"checked_specializations\":");
                format(out, cov.checked, ",\"unchecked_generic_bodies\":", cov.unchecked, ",\"unsupported\":[");
                append_unsupported(out, cov); out.append("]}\n");
            }
        } else {
            out.append("{\"kind\":\"coverage\",\"schema_version\":1,\"path\":null,\"parse\":\"not_run\",\"check\":\"not_run\",\"checked_specializations\":null,\"unchecked_generic_bodies\":null,\"unsupported\":[]}\n");
        }
        out.append("{\"kind\":\"error\",\"schema_version\":1,\"code\":"); json::format_string(out, code);
        out.append(",\"message\":"); json::format_string(out, message); format(out, ",\"exit_status\":", status, "}\n");
        format(out, "{\"kind\":\"summary\",\"schema_version\":1,\"findings\":0,\"suppressed\":0,\"errors\":1,\"exit_status\":", status, "}\n");
    } else {
        out.append("goose lint: "); out.append(message); out.push('\n');
    }
    write_lint_output(output, out);
    return status;
}

fn run() -> i64 {
    let argv = args();
    var facts_path: const u8[:] = ""; var output_path: const u8[:] = "";
    var format_name: const u8[:] = "text";
    var entry: const u8[:] = "unknown"; var revision: const u8[:] = "unknown"; var profile: const u8[:] = "O1";
    var cli_group = false;
    var config_path: const u8[:] = ""; var baseline_path: const u8[:] = "";
    var config_baseline: u8[>..] = []; var config_contracts: u8[>..] = [];
    var require_complete = false; var write_baseline = false;
    var option_error: const u8[:] = "";
    groups.clear(); allow.clear(); deny.clear(); configured_groups.clear();
    enabled.clear(); config_allow.clear(); config_deny.clear();
    contract_apis.clear(); project_contracts_required = false; configured_severities.clear();
    var i = 1;
    while i < argv.len {
        let arg = argv[i];
        if arg == "--facts" || arg == "--output" || arg == "--entry" || arg == "--revision" || arg == "--profile" ||
           arg == "--format" || arg == "--group" ||
           arg == "--allow" || arg == "--deny" || arg == "--config" || arg == "--baseline" {
            if i + 1 >= argv.len { option_error = "option requires a value"; break; }
            i++; let value = argv[i];
            if value.len == 0 || value[0] == '-' { option_error = "option requires a value"; break; }
            if arg == "--facts" { if facts_path.len != 0 { option_error = "duplicate --facts"; break; } facts_path = value; }
            else if arg == "--output" { if output_path.len != 0 { option_error = "duplicate --output"; break; } output_path = value; }
            else if arg == "--entry" { entry = keep(value); }
            else if arg == "--revision" { revision = keep(value); }
            else if arg == "--profile" { profile = keep(value); }
            else if arg == "--format" { format_name = value; }
            else if arg == "--group" { cli_group = true; if !known_group(value) { option_error = "unknown rule group"; break; } groups.push(value); }
            else if arg == "--allow" { if !known_rule(value) { option_error = "unknown rule ID in --allow"; break; } if !runnable_rule(value) { option_error = "rule ID in --allow is not available in this build"; break; } allow.push(value); }
            else if arg == "--deny" { if !known_rule(value) { option_error = "unknown rule ID in --deny"; break; } if !runnable_rule(value) { option_error = "rule ID in --deny is not available in this build"; break; } deny.push(value); }
            else if arg == "--config" { if config_path.len != 0 { option_error = "duplicate --config"; break; } config_path = value; }
            else if arg == "--baseline" { if baseline_path.len != 0 { option_error = "duplicate --baseline"; break; } baseline_path = value; }
        } else if arg == "--require-complete" { require_complete = true; }
        else if arg == "--write-baseline" { write_baseline = true; }
        else { option_error = "unknown companion option"; break; }
        i++;
    }
    if format_name != "text" && format_name != "jsonl" { option_error = "--format must be text or jsonl"; }
    if output_path.len == 0 { return 3; }
    var fallback: Facts = Facts { revision: revision, profile: profile };
    if option_error.len != 0 { return emit_error(output_path, format_name, revision, entry, profile, "invalid_config", option_error, 3, fallback, false); }
    if facts_path.len == 0 { return emit_error(output_path, format_name, revision, entry, profile, "invalid_config", "--facts is required", 3, fallback, false); }
    if config_path.len != 0 {
        var config_error: u8[>..] = [];
        if !load_config(config_path, configured_groups, enabled, config_allow, config_deny,
                        config_baseline, config_contracts, configured_severities, config_error) {
            return emit_error(output_path, format_name, revision, entry, profile, "invalid_config", config_error, 3, fallback, false);
        }
        if !load_contracts(config_contracts, config_error) {
            return emit_error(output_path, format_name, revision, entry, profile, "invalid_config", config_error, 3, fallback, false);
        }
    }
    for code in allow { if contains_value(deny, code) { option_error = "a rule cannot be both --allow and --deny"; } }
    if option_error.len != 0 { return emit_error(output_path, format_name, revision, entry, profile, "invalid_config", option_error, 3, fallback, false); }
    if !cli_group {
        if configured_groups.len > 0 { groups.append(configured_groups); }
        else { groups.push("existing"); groups.push("correctness"); groups.push("suspicious"); }
    }
    project_contracts_required = rule_selected("view_before_append_argument", groups, enabled,
        config_allow, config_deny, allow, deny) ||
        rule_selected("foreign_container_index", groups, enabled,
        config_allow, config_deny, allow, deny);
    let resolved_baseline_path = if baseline_path.len > 0 { keep(baseline_path) } else { keep(config_baseline) };
    if write_baseline && resolved_baseline_path.len == 0 {
        return emit_error(output_path, format_name, revision, entry, profile, "invalid_config", "--write-baseline requires --baseline or config baseline", 3, fallback, false);
    }

    var raw: u8[>..] = [];
    if !read_file(facts_path, raw) { return emit_error(output_path, format_name, revision, entry, profile, "tool_failure", "cannot read compiler facts", 4, fallback, false); }
    var facts: Facts = Facts { revision: revision, profile: profile };
    var fact_error: u8[>..] = [];
    if !parse_facts(raw, facts, fact_error) {
        return emit_error(output_path, format_name, facts.revision, entry, facts.profile, "tool_failure", fact_error, 4, facts, false);
    }
    if entry_facts.len == 0 { return emit_error(output_path, format_name, facts.revision, "unknown", facts.profile, "tool_failure", "facts header has no entry", 4, facts, false); }
    if !validate_contract_calls(fact_error) {
        return emit_error(output_path, format_name, facts.revision, entry_facts[0], facts.profile,
            "invalid_config", fact_error, 3, facts, true);
    }

    var diagnostics: OutputDiagnostic[>..] = [];
    let findings, suppressed = collect_diagnostics(diagnostics, facts, groups, enabled, config_allow, config_deny,
        configured_severities, allow, deny);
    var stale_baseline = 0;
    if write_baseline {
        if !write_baseline_file(resolved_baseline_path, diagnostics, facts) {
            return emit_error(output_path, format_name, facts.revision, entry_facts[0], facts.profile,
                "tool_failure", "cannot atomically write baseline", 4, facts, true);
        }
    } else if resolved_baseline_path.len > 0 {
        var baseline_error: u8[>..] = [];
        if !load_baseline(resolved_baseline_path, baseline_error) {
            return emit_error(output_path, format_name, facts.revision, entry_facts[0], facts.profile,
                "invalid_config", baseline_error, 3, facts, true);
        }
        stale_baseline = apply_baseline(diagnostics, facts, baseline_error);
        if stale_baseline < 0 {
            return emit_error(output_path, format_name, facts.revision, entry_facts[0], facts.profile,
                "invalid_config", baseline_error, 3, facts, true);
        }
    }
    var denied = 0; var baselined = 0;
    for diagnostic in diagnostics {
        if diagnostic.baselined { baselined++; }
        else if !diagnostic.suppressed && rule_denied(diagnostic.code, config_allow, config_deny, allow, deny,
                                                       configured_severities) { denied++; }
    }
    if stale_baseline > 0 && rule_denied("stale_baseline", config_allow, config_deny, allow, deny,
                                         configured_severities) { denied++; }
    var unsupported = project_contracts_required && contract_apis.len == 0;
    for cov in coverage_facts { if coverage_incomplete(cov) { unsupported = true; } }
    var status = if denied > 0 { 1 } else { 0 };
    if require_complete && unsupported { status = 4; }
    var out: u8[>..] = [];
    if format_name == "jsonl" {
        out.append("{\"kind\":\"header\",\"schema_version\":1,\"tool\":\"goose-lint\",\"compiler_revision\":");
        json::format_string(out, facts.revision); out.append(",\"entries\":[");
        var first = true; for path in entry_facts { if !first { out.push(','); } first = false; json::format_string(out, path); }
        out.append("],\"profile\":"); json::format_string(out, facts.profile); out.append("}\n");
        for diagnostic in diagnostics { emit_diagnostic(out, diagnostic, facts); }
        if write_baseline {
            out.append("{\"kind\":\"baseline\",\"schema_version\":1,\"written\":true,\"entries\":");
            format(out, baseline_count(diagnostics), "}\n");
        }
        for entry in baseline_entries {
            if !entry.matched {
                out.append("{\"kind\":\"baseline\",\"schema_version\":1,\"status\":\"stale\",\"fingerprint\":");
                json::format_string(out, entry.fingerprint);
                out.append(",\"code\":"); json::format_string(out, entry.code);
                out.append(",\"path\":"); json::format_string(out, entry.path);
                out.append("}\n");
            }
        }
        for cov in coverage_facts {
            out.append("{\"kind\":\"coverage\",\"schema_version\":1,\"path\":"); json::format_string(out, cov.path);
            out.append(",\"parse\":\"complete\",\"check\":");
            json::format_string(out, if coverage_incomplete(cov) { "partial" } else { "complete" });
            format(out, ",\"checked_specializations\":", cov.checked,
                   ",\"unchecked_generic_bodies\":", cov.unchecked, ",\"unsupported\":[");
            append_unsupported(out, cov); out.append("]}\n");
        }
        if require_complete && unsupported {
            out.append("{\"kind\":\"error\",\"schema_version\":1,\"code\":\"analysis_incomplete\",\"message\":\"required analyses have unsupported facts or unchecked generic bodies\",\"exit_status\":4}\n");
        }
        format(out, "{\"kind\":\"summary\",\"schema_version\":1,\"findings\":", findings,
               ",\"suppressed\":", suppressed, ",\"baselined\":", baselined,
               ",\"stale_baseline_entries\":", stale_baseline,
               ",\"errors\":", if require_complete && unsupported { 1 } else { 0 }, ",\"exit_status\":", status, "}\n");
    } else {
        for diagnostic in diagnostics {
            format(out, source_at(facts, diagnostic.file_id), ":", diagnostic.start_line, ": warning[", diagnostic.code, "]: ", diagnostic.message);
            if diagnostic.suppressed { format(out, " [suppressed: ", diagnostic.suppression_reason, "]"); }
            else if diagnostic.baselined { out.append(" [baseline]"); }
            out.push('\n');
        }
        if write_baseline { format(out, "wrote baseline: ", resolved_baseline_path, "\n"); }
        for entry in baseline_entries {
            if !entry.matched { format(out, "stale baseline: ", entry.path, " [", entry.code, "] ", entry.fingerprint, "\n"); }
        }
        format(out, "checked ", warning_facts.len, " compiler warnings; ", findings, " selected findings (", suppressed, " suppressed)\n");
        if require_complete && unsupported { out.append("analysis incomplete: required facts or generic coverage are unavailable\n"); }
    }
    if out.len > MAX_OUTPUT { return emit_error(output_path, format_name, facts.revision, entry_facts[0], facts.profile, "tool_failure", "lint output exceeds 256 MiB", 4, facts, true); }
    if !write_lint_output(output_path, out) { return 4; }
    return status;
}

fn main() {
    let status = run();
    if status != 0 { exit(status); }
}
