#!/bin/sh
# Check flat-struct source, Core, GIR-H, GIR-L, and native behavior.
#
#   s8_struct_contract.sh [GOOSE [GOOSE_SEMANTICS [CLANG]]]
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
goose=${1:-$root/build/goose}
semantics=${2:-$root/semantics/.lake/build/bin/goose-semantics}
clang=${3:-${CLANG:-clang}}
jaq=${JAQ:-jaq}

[ -x "$goose" ] || { echo "missing Goose compiler: $goose" >&2; exit 2; }
command -v "$jaq" >/dev/null 2>&1 || { echo "missing jaq executable: $jaq" >&2; exit 2; }
command -v "$clang" >/dev/null 2>&1 || { echo "missing Clang executable: $clang" >&2; exit 2; }

workroot=$root/.work/tmp
mkdir -p "$workroot"
export TMPDIR=$workroot
work=$(mktemp -d "$workroot/s8-struct.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM

expect_unsupported() {
    source=$1
    feature=$2
    label=$3
    core=$work/$label.core.json
    high=$work/$label.high.json
    low=$work/$label.low.json
    log=$work/$label.log

    set +e
    "$goose" --emit-core "$core" --emit-gir-high "$high" --emit-gir-low "$low" \
        --check "$source" >"$log" 2>&1
    status=$?
    set -e

    [ "$status" -ne 0 ] || { echo "FAIL $label: unexpectedly exported" >&2; exit 1; }
    case $(cat "$log") in
        *"unsupported in core-pilot: $feature"*) ;;
        *) echo "FAIL $label: missing core-pilot diagnostic $feature" >&2; cat "$log" >&2; exit 1 ;;
    esac
    for artifact in "$core" "$high" "$low"; do
        [ ! -e "$artifact" ] || { echo "FAIL $label: published $artifact" >&2; exit 1; }
    done
}

expect_legacy_run() {
    source=$1
    expected=$2
    label=$3
    abort_message=$4
    output=$work/$label.out
    log=$work/$label.log

    set +e
    "$goose" "$source" >"$output" 2>"$log"
    status=$?
    set -e

    cmp "$expected" "$output"
    if [ -n "$abort_message" ]; then
        [ "$status" -ne 0 ] || { echo "FAIL $label: expected an abort" >&2; exit 1; }
        case $(cat "$log") in
            *"goose runtime error: $abort_message"*) ;;
            *) echo "FAIL $label: missing abort diagnostic $abort_message" >&2; cat "$log" >&2; exit 1 ;;
        esac
    else
        [ "$status" -eq 0 ] || { echo "FAIL $label: exit status $status" >&2; cat "$log" >&2; exit 1; }
    fi
}

expect_export() {
    label=$1
    shift
    log=$work/$label.log
    if ! "$goose" "$@" >"$log" 2>&1; then
        echo "FAIL $label: export failed" >&2
        cat "$log" >&2
        exit 1
    fi
}

expect_semantics_line() {
    label=$1
    expected_status=$2
    expected_line=$3
    shift 3
    output=$work/$label.json
    log=$work/$label.log

    if "$semantics" "$@" >"$output" 2>"$log"; then
        status=0
    else
        status=$?
    fi
    actual=$(cat "$output")
    if [ "$status" -ne "$expected_status" ] || [ "$actual" != "$expected_line" ]; then
        echo "FAIL $label: status $status, output $actual" >&2
        cat "$log" >&2
        exit 1
    fi
}

expect_semantics_prefix() {
    label=$1
    expected_status=$2
    expected_prefix=$3
    shift 3
    output=$work/$label.actual.json
    log=$work/$label.log

    if "$semantics" "$@" >"$output" 2>"$log"; then
        status=0
    else
        status=$?
    fi
    actual=$(cat "$output")
    case $actual in
        "$expected_prefix"*)
            [ "$status" -eq "$expected_status" ] || {
                echo "FAIL $label: status $status, expected $expected_status" >&2
                cat "$log" >&2
                exit 1
            } ;;
        *)
            echo "FAIL $label: expected output beginning $expected_prefix, got $actual" >&2
            cat "$log" >&2
            exit 1 ;;
    esac
}

expect_malformed() {
    label=$1
    command=$2
    module=$3
    expect_semantics_prefix "$label" 2 '["malformed",' "$command" "$module"
}

expect_unsupported "$root/test/codegen/s8_struct_whole_const_local.goose" \
    struct-whole-const whole-const-local
expect_unsupported "$root/test/codegen/s8_struct_whole_const_parameter.goose" \
    struct-whole-const whole-const-parameter
expect_unsupported "$root/test/codegen/s8_struct_whole_const_result.goose" \
    struct-whole-const whole-const-result
expect_unsupported "$root/test/codegen/s8_struct_temporary_projection.goose" \
    struct-temporary-projection temporary-projection

# Keep the nested-const rejection and direct field-const source checks in the
# same standard-discovered S8 gate as the flat-struct cross-layer cases.
sh "$root/test/gir/source/check.sh" "$goose"

# These fixtures isolate field behavior, copy snapshots, and ordered defaults.
expect_legacy_run "$root/test/codegen/flat_struct_fields.goose" \
    "$root/test/expected/flat_struct_fields.out" struct-fields ""
expect_legacy_run "$root/test/codegen/flat_struct_copy.goose" \
    "$root/test/expected/flat_struct_copy.out" struct-copy ""
expect_legacy_run "$root/test/codegen/flat_struct_initializer_order.goose" \
    "$root/test/expected/flat_struct_initializer_order.out" struct-default-order middle
expect_legacy_run "$root/test/codegen/s8_struct_whole_const_local.goose" \
    "$root/test/expected/s8_struct_whole_const_local.out" legacy-whole-const-local ""
expect_legacy_run "$root/test/codegen/s8_struct_whole_const_parameter.goose" \
    "$root/test/expected/s8_struct_whole_const_parameter.out" legacy-whole-const-parameter ""
expect_legacy_run "$root/test/codegen/s8_struct_whole_const_result.goose" \
    "$root/test/expected/s8_struct_whole_const_result.out" legacy-whole-const-result ""
expect_legacy_run "$root/test/codegen/s8_struct_temporary_projection.goose" \
    "$root/test/expected/s8_struct_temporary_projection.out" legacy-temporary-projection ""

# Pipeline rejection must not publish any artifact, even when all writers are
# requested together.
pipeline_core=$work/pipeline.core.json
pipeline_high=$work/pipeline.high.json
pipeline_low=$work/pipeline.low.json
set +e
"$goose" --pipeline gir --emit-core "$pipeline_core" --emit-gir-high "$pipeline_high" \
    --emit-gir-low "$pipeline_low" --check \
    "$root/test/codegen/s8_struct_whole_const_local.goose" >"$work/pipeline.log" 2>&1
pipeline_status=$?
set -e
[ "$pipeline_status" -ne 0 ] || { echo "FAIL pipeline: unexpectedly exported" >&2; exit 1; }
case $(cat "$work/pipeline.log") in
    *"unsupported in pipeline gir: struct-whole-const"*) ;;
    *) echo "FAIL pipeline: missing GIR diagnostic" >&2; cat "$work/pipeline.log" >&2; exit 1 ;;
esac
for artifact in "$pipeline_core" "$pipeline_high" "$pipeline_low"; do
    [ ! -e "$artifact" ] || { echo "FAIL pipeline: published $artifact" >&2; exit 1; }
done

# Pin a nonempty pilot artifact containing a global, implementations, and
# contexts; an empty-module check cannot protect representative wire bytes.
pilot_source=$here/golden/first.goose
pilot_golden=$here/golden/first.core.json
shrink_core=$root/test/semantics/golden/shrink_replace.core.json
expect_export pilot --emit-core "$work/pilot.core.json" --check "$pilot_source"
expect_export pilot-again --emit-core "$work/pilot-again.core.json" --check "$pilot_source"
cmp "$pilot_golden" "$work/pilot.core.json"
cmp "$work/pilot.core.json" "$work/pilot-again.core.json"
"$jaq" -e '
    .[0] == "module" and .[1] == "goose-core/0.2" and .[2] == "core-pilot" and
    length == 10 and
    (.[3] | length) > 0 and (.[4] | length) > 0 and
    (.[5] | length) > 0 and (.[6] | length) > 0 and (.[7] | length) > 0
' "$work/pilot.core.json" >/dev/null

# Core and GIR pilot artifacts keep their earlier table shapes and reject
# shrink-only types, operations, and abort kinds during decoding.
for tag in growshrink limited; do
    if [ "$tag" = growshrink ]; then
        filter='.[4] += [["growshrink",0]]'
    else
        filter='.[4] += [["limited",0,1]]'
    fi
    "$jaq" "$filter" "$work/pilot.core.json" >"$work/core-pilot-$tag.json"
    expect_malformed "core-pilot-$tag" validate "$work/core-pilot-$tag.json"
done
"$jaq" '.[4] += [["struct",0]]' "$work/pilot.core.json" >"$work/core-pilot-struct-type.json"
expect_malformed core-pilot-struct-type validate "$work/core-pilot-struct-type.json"
"$jaq" '.[0:5] + [[]] + .[5:]' "$work/pilot.core.json" >"$work/core-pilot-struct-table.json"
expect_malformed core-pilot-struct-table validate "$work/core-pilot-struct-table.json"
"$jaq" '.[6][0][5][2][0][2] = ["e_struct"]' "$work/pilot.core.json" \
    >"$work/core-pilot-e-struct.json"
expect_malformed core-pilot-e-struct validate "$work/core-pilot-e-struct.json"
"$jaq" '.[6][0][5][2][0] = ["s_expr",["e_read",["p_field"]],0]' \
    "$work/pilot.core.json" >"$work/core-pilot-p-field.json"
expect_malformed core-pilot-p-field validate "$work/core-pilot-p-field.json"
for tag in s_pop_n s_resize s_clear s_assign_whole; do
    "$jaq" --arg tag "$tag" '.[6][0][5][2][0] = [$tag]' "$work/pilot.core.json" \
        >"$work/core-pilot-$tag.json"
    expect_malformed "core-pilot-$tag" validate "$work/core-pilot-$tag.json"
done
"$jaq" '.[6][0][5][2][0] = ["s_expr",["e_pop"],0]' "$work/pilot.core.json" \
    >"$work/core-pilot-e-pop.json"
expect_malformed core-pilot-e-pop validate "$work/core-pilot-e-pop.json"
"$jaq" '.[7][0][5][2][0][2] = ["e_push",["p_local",0],["e_lit",0,"1"]]' \
    "$shrink_core" >"$work/core-shrink-e-push-missing-origin.json"
expect_malformed core-shrink-e-push-missing-origin validate \
    "$work/core-shrink-e-push-missing-origin.json"

gir_pilot=$root/test/gir/golden/gir_assert_fail.gir-h.json
for tag in growshrink limited; do
    if [ "$tag" = growshrink ]; then
        filter='.[4] += [["growshrink",0]]'
    else
        filter='.[4] += [["limited",0,1]]'
    fi
    "$jaq" "$filter" "$gir_pilot" >"$work/gir-pilot-$tag.json"
    expect_malformed "gir-pilot-$tag" gir-validate "$work/gir-pilot-$tag.json"
done
"$jaq" '.[4] += [["struct",0]]' "$gir_pilot" >"$work/gir-pilot-struct-type.json"
expect_malformed gir-pilot-struct-type gir-validate "$work/gir-pilot-struct-type.json"
"$jaq" '.[0:5] + [[]] + .[5:]' "$gir_pilot" >"$work/gir-pilot-struct-table.json"
expect_malformed gir-pilot-struct-table gir-validate "$work/gir-pilot-struct-table.json"
for tag in i_struct i_field i_pop x_pop_n x_resize x_clear x_replace; do
    "$jaq" --arg tag "$tag" '.[6][0][6][0][2][0] = [$tag]' "$gir_pilot" \
        >"$work/gir-pilot-$tag.json"
    expect_malformed "gir-pilot-$tag" gir-validate "$work/gir-pilot-$tag.json"
done
for kind in pop_empty pop_n_range resize_negative resize_fill capacity; do
    "$jaq" --arg kind "$kind" '.[6][0][6][2][2][0][1] = $kind' "$gir_pilot" \
        >"$work/gir-pilot-abort-$kind.json"
    expect_malformed "gir-pilot-abort-$kind" gir-validate "$work/gir-pilot-abort-$kind.json"
done

# A packed u8/i64/i16 record exercises an unaligned i64 field read and write.
# Compare repeated exports to catch nondeterministic type or instruction IDs.
struct_source=$root/test/codegen/flat_struct_fields.goose
emit_struct_artifacts() {
    prefix=$1
    expect_export "$prefix" --emit-core "$work/$prefix.core.json" \
        --emit-gir-high "$work/$prefix.high.json" --emit-gir-low "$work/$prefix.low.json" \
        --check "$struct_source"
}
emit_struct_artifacts struct
emit_struct_artifacts struct-again
cmp "$work/struct.core.json" "$work/struct-again.core.json"
cmp "$work/struct.high.json" "$work/struct-again.high.json"
cmp "$work/struct.low.json" "$work/struct-again.low.json"

"$jaq" -e '
    .[0] == "module" and .[1] == "goose-core/0.2" and .[2] == "core-shrink" and
    length == 11 and (.[5] | length) == 1 and .[5][0][0] == "struct_def" and
    .[5][0][1] == 11 and
    (.[5][0][2] | map([.[0], .[2], .[3], .[4]]) == [
        ["field", "var", "mut", 0],
        ["field", "var", "mut", 1],
        ["field", "let", "const", 9]
    ])
' "$work/struct.core.json" >/dev/null
"$jaq" -e '
    .[0] == "module" and .[1] == "gir-h/0.3" and .[2] == "core-shrink" and
    length == 10 and (.[5] | length) == 1 and .[5][0][1] == 11 and
    (tostring | contains("i_struct") and contains("i_field"))
' "$work/struct.high.json" >/dev/null

# The shrink profile requires exactly one struct table in both schemas.
"$jaq" '.[0:5] + .[6:]' "$work/struct.core.json" >"$work/core-shrink-missing-structs.json"
expect_malformed core-shrink-missing-structs validate "$work/core-shrink-missing-structs.json"
"$jaq" '.[0:5] + [.[5]] + .[5:]' "$work/struct.core.json" >"$work/core-shrink-extra-structs.json"
expect_malformed core-shrink-extra-structs validate "$work/core-shrink-extra-structs.json"
"$jaq" '.[0:5] + .[6:]' "$work/struct.high.json" >"$work/gir-shrink-missing-structs.json"
expect_malformed gir-shrink-missing-structs gir-validate "$work/gir-shrink-missing-structs.json"
"$jaq" '.[0:5] + [.[5]] + .[5:]' "$work/struct.high.json" >"$work/gir-shrink-extra-structs.json"
expect_malformed gir-shrink-extra-structs gir-validate "$work/gir-shrink-extra-structs.json"

"$jaq" -e '
    .[0] == "module" and .[1] == "gir-l/0.2" and .[2] == "core-shrink" and
    (tostring | [contains("struct_def"), contains("i_struct"), contains("i_field")]) ==
        [false, false, false] and
    (.[4] | all(.[]; .[0] != "struct")) and
    (.[6][0][5] | any(.[]; .[0] == "m_bytes" and .[1] == 11)) and
    (.[6][0][7][0][2] | any(.[]; .[0] == "l_copy")) and
    (.[6][0][7][0][2] | any(.[]; .[0] == "l_get")) and
    (.[6][0][7][0][2] | any(.[]; .[0] == "l_set")) and
    (.[6][0][7][0][2] | all(.[]; .[0] != "l_load" and .[0] != "l_store"))
' "$work/struct.low.json" >/dev/null

# Compile the actual GIR pipeline through Clang at both optimization levels.
# The same program's field update must remain safe under Clang's alignment UBSan.
gir_c=$work/struct-gir.c
if ! "$goose" --pipeline gir --standalone -o "$gir_c" "$struct_source" >"$work/gir-build.log" 2>&1; then
    echo "FAIL GIR C emission" >&2
    cat "$work/gir-build.log" >&2
    exit 1
fi
for opt in 0 2; do
    program=$work/struct-gir-O$opt
    if ! "$clang" "-O$opt" "$gir_c" -lm -pthread -o "$program" >"$work/clang-O$opt.log" 2>&1; then
        echo "FAIL Clang -O$opt" >&2
        cat "$work/clang-O$opt.log" >&2
        exit 1
    fi
    if ! "$program" >"$work/native-O$opt.out" 2>"$work/native-O$opt.err"; then
        echo "FAIL native GIR -O$opt" >&2
        cat "$work/native-O$opt.err" >&2
        exit 1
    fi
    cmp "$root/test/expected/flat_struct_fields.out" "$work/native-O$opt.out"
done

alignment_program=$work/struct-gir-alignment
if ! "$clang" -O0 -fsanitize=alignment -fno-sanitize-recover=alignment \
    "$gir_c" -lm -pthread -o "$alignment_program" >"$work/clang-alignment.log" 2>&1; then
    echo "FAIL Clang alignment-sanitizer build" >&2
    cat "$work/clang-alignment.log" >&2
    exit 1
fi
if ! "$alignment_program" >"$work/alignment.out" 2>"$work/alignment.err"; then
    echo "FAIL packed field access under Clang alignment sanitizer" >&2
    cat "$work/alignment.err" >&2
    exit 1
fi
[ ! -s "$work/alignment.err" ] || {
    echo "FAIL alignment sanitizer wrote diagnostics" >&2
    cat "$work/alignment.err" >&2
    exit 1
}
cmp "$root/test/expected/flat_struct_fields.out" "$work/alignment.out"

if [ -x "$semantics" ]; then
    # Lean decodes and validates C++ Core, evaluates both Core and GIR, lowers Core
    # to the same GIR-H bytes, reencodes C++ GIR-H, and checks their outcomes agree.
expected_run='["done",["returned"],"1 42 7\n"]'
expect_semantics_line core-validate 0 '["ok"]' validate "$work/struct.core.json"
expect_semantics_line core-run 0 "$expected_run" run "$work/struct.core.json"
if ! "$semantics" lower "$work/struct.core.json" >"$work/lean-lowered.high.json" \
    2>"$work/lean-lower.log"; then
    echo "FAIL Lean Core lower" >&2
    cat "$work/lean-lower.log" >&2
    cat "$work/lean-lowered.high.json" >&2
    exit 1
fi
cmp "$work/struct.high.json" "$work/lean-lowered.high.json"
expect_semantics_line gir-validate 0 '["ok"]' gir-validate "$work/struct.high.json"
expect_semantics_line gir-run 0 "$expected_run" gir-run "$work/struct.high.json"
if ! "$semantics" gir-reencode "$work/struct.high.json" >"$work/lean-reencoded.high.json" \
    2>"$work/gir-reencode.log"; then
    echo "FAIL Lean GIR reencode" >&2
    cat "$work/gir-reencode.log" >&2
    cat "$work/lean-reencoded.high.json" >&2
    exit 1
fi
cmp "$work/struct.high.json" "$work/lean-reencoded.high.json"
expect_semantics_line agree 0 '["agree",["done",["returned"],"1 42 7\n"]]' \
    agree "$work/struct.core.json" "$work/struct.high.json"

# Exercise the GIR-H verifier's independently decoded whole-replacement cases.
if ! "$semantics" lower "$shrink_core" >"$work/shrink.high.json" \
    2>"$work/shrink-lower.log"; then
    echo "FAIL Lean shrink Core lower" >&2
    cat "$work/shrink-lower.log" >&2
    cat "$work/shrink.high.json" >&2
    exit 1
fi
expect_semantics_line shrink-gir-validate 0 '["ok"]' gir-validate "$work/shrink.high.json"
"$jaq" -e '
    ([.[7][] | .[6][] | .[2][] | select(.[0] == "x_clear")] | length) == 1 and
    ([.[7][] | .[6][] | .[2][] | select(.[0] == "x_replace")] | length) == 1
' "$work/shrink.high.json" >/dev/null

# A replacement without a clear must fail even when its run is a literal.
"$jaq" '.[7] |= map(.[6] |= map(.[2] |= map(select(.[0] != "x_clear"))))' \
    "$work/shrink.high.json" >"$work/gir-replace-no-clear.json"
expect_semantics_prefix gir-replace-no-clear 5 '["rejected","GIR-V060",' \
    gir-validate "$work/gir-replace-no-clear.json"

# A second slot address aliases the cleared owner; pushing through it kills
# the empty fact before the otherwise literal replacement.
"$jaq" '
    (.[4] | to_entries[] |
        select(.value[0] == "int" and .value[1] == "i64") | (.key | tonumber)) as $i64
    | .[7] |= map(
        . as $function
        | if ([$function[6][] | .[2][] | select(.[0] == "x_clear")] | length) == 0 then
            $function
          else
            ([$function[6][] | .[2][] | select(.[0] == "x_clear")][0]) as $clear
            | $clear[1] as $owner
            | ([$function[6][] | .[2][] |
                select(.[0] == "i_slot" and .[1] == $owner)][0][2]) as $slot
            | ([$function[6][] |
                (.[1][] | .[1]),
                (.[2][] | select(.[0] | startswith("i_")) | .[1])] | max + 1) as $next
            | .[6] |= map(
                .[2] |= map(
                    if .[0] == "x_clear" then
                        ., ["i_slot",$next,$slot],
                        ["i_int",$next+1,$i64,"7"],
                        ["i_push",$next+2,$next,$next+1,$clear[2]]
                    else . end
                )
              )
          end
      )
' "$work/shrink.high.json" >"$work/gir-replace-alias-growth.json"
expect_semantics_prefix gir-replace-alias-growth 5 '["rejected","GIR-V060",' \
    gir-validate "$work/gir-replace-alias-growth.json"

# A literal run is invalid when one of its values is loaded from the receiver
# after clearing it.
"$jaq" '
    (.[4] | to_entries[] |
        select(.value[0] == "int" and .value[1] == "i64") | (.key | tonumber)) as $i64
    | .[7] |= map(
        . as $function
        | ([$function[6][] | .[2][] | select(.[0] == "x_clear")][0]) as $clear
        | $clear[1] as $owner
        | ([$function[6][] |
            (.[1][] | .[1]),
            (.[2][] | select(.[0] | startswith("i_")) | .[1])] | max + 1) as $next
        | ([$function[6][] | .[2][] | select(.[0] == "x_replace")][0][2]) as $run
        | .[6] |= map(
            .[2] |= map(
                if .[0] == "x_clear" then
                    .,
                    ["i_snap",$next,"owner",$owner],
                    ["i_int",$next+1,$i64,"0"],
                    ["i_index",$next+2,$next,$next+1,$clear[2]],
                    ["i_load",$next+3,$next+2]
                elif .[0] == "i_arr" and .[1] == $run then
                    .[3] = [$next+3]
                else . end
            )
          )
      )
' "$work/shrink.high.json" >"$work/gir-replace-dependent-run.json"
expect_semantics_prefix gir-replace-dependent-run 5 '["rejected","GIR-V060",' \
    gir-validate "$work/gir-replace-dependent-run.json"

# Forge well-decoded Core mutations from the C++ artifact and route them through
# Lean's validator, keeping type and permission checks independent of C++ tests.
"$jaq" -e '
    .[7][0][5][2][1][0] == "s_assign_op" and
    .[7][0][5][2][1][2][0] == "p_field" and
    .[7][0][5][2][1][2][2] == 1 and
    .[7][0][5][2][1][3][0] == "e_lit" and .[7][0][5][2][1][3][1] == 1
' "$work/struct.core.json" >/dev/null
"$jaq" '.[7][0][5][2][1][3][1] = 0' "$work/struct.core.json" >"$work/forged-type.core.json"
"$jaq" '.[7][0][5][2][1][2][2] = 2 | .[7][0][5][2][1][3][1] = 2' \
    "$work/struct.core.json" >"$work/forged-mut.core.json"
expect_semantics_prefix forged-core-type 5 '["rejected","V-TYPE",' \
    validate "$work/forged-type.core.json"
expect_semantics_prefix forged-core-mut 5 '["rejected","V-MUT",' \
    validate "$work/forged-mut.core.json"

    echo "s8 structs: Lean Core/GIR validation, parity, and mutation checks ok"
else
    echo "skip Lean Core/GIR validation and mutation checks: missing $semantics (build with lake build goose-semantics)"
fi

echo "s8 structs: source export, Core/GIR shape, packed native access, and sanitizer ok"
