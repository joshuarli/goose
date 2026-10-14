#!/bin/sh
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
goose=${1:-$root/build/goose}
tool=${2:-$root/semantics/.lake/build/bin/goose-semantics}
jaq=${JAQ:-jaq}
work=$root/.work/tmp/gir-bce
mkdir -p "$work"
TMPDIR=$root/.work/tmp
export TMPDIR

fail() {
    echo "FAIL $*" >&2
    exit 1
}

run_result() {
    file=$1
    profile=$2
    fuel=$3
    output=$4
    validation=$5
    set +e
    "$tool" gir-run "$file" --numeric "$profile" --fuel "$fuel" $validation >"$output"
    result=$?
    set -e
    case $result in
        0|3) ;;
        *) cat "$output" >&2; fail "$file $profile fuel $fuel returned $result" ;;
    esac
    printf '%s' "$result"
}

for module in "$here"/../invalid/gir_rejected_v080_*.json; do
    set +e
    rejected=$("$tool" gir-validate "$module")
    result=$?
    set -e
    [ "$result" -eq 5 ] || fail "$module was not rejected"
    printf '%s\n' "$rejected" | "$jaq" -e '.[0:2] == ["rejected", "GIR-V080"]' >/dev/null ||
        fail "$module did not report GIR-V080"
done

for name in returned aborted called looping call_kill scope_kill loop_counter; do
    high=$work/$name.gir-h
    checked=$work/$name.checked.gir-h
    roundtrip=$work/$name.roundtrip.gir-h
    "$goose" -O0 --pipeline gir --emit-gir-high "$high" --check "$here/$name.goose" \
        >"$work/$name.compiler.out" 2>"$work/$name.compiler.err" || {
        cat "$work/$name.compiler.out" "$work/$name.compiler.err" >&2
        fail "$name source export"
    }
    "$jaq" -e '.[0:3] == ["module", "gir-h/0.4", "core-pilot"]' "$high" >/dev/null ||
        fail "$name did not export the pilot profile"
    proven=$("$jaq" '[.. | arrays | select(.[0]? == "i_index_proven")] | length' "$high")
    case $name in
        returned|aborted|called|looping)
            [ "$proven" -gt 0 ] || fail "$name emitted no proven index"
            "$jaq" -e '[.. | arrays | select(.[0]? == "certificate")] | length > 0' "$high" >/dev/null ||
                fail "$name emitted no certificate"
            ;;
        *) [ "$proven" -eq 0 ] || fail "$name eliminated an index after a conservative kill" ;;
    esac
    [ "$("$tool" gir-validate "$high")" = '["ok"]' ] || fail "$name independent validation"
    "$tool" gir-reencode "$high" >"$roundtrip"
    [ "$("$jaq" -c . "$high")" = "$("$jaq" -c . "$roundtrip")" ] || fail "$name roundtrip"
    "$jaq" -c 'walk(if type == "array" and .[0]? == "i_index_proven" then
        ["i_index", .[1], .[2], .[3], []] else . end)' "$high" >"$checked"
    for profile in release debug; do
        for fuel in 0 1 8 32 256; do
            original=$work/$name.$profile.$fuel.original
            replacement=$work/$name.$profile.$fuel.checked
            first=$(run_result "$high" "$profile" "$fuel" "$original" '')
            second=$(run_result "$checked" "$profile" "$fuel" "$replacement" '--no-validate')
            [ "$first" = "$second" ] && cmp -s "$original" "$replacement" ||
                fail "$name $profile fuel $fuel changed whole-run observables"
        done
        result=$work/$name.$profile.256.original
        case $name in
            returned) expectation='.[0:2] == ["done", ["returned"]] and .[2] == "7\n"' ;;
            aborted) expectation='.[0] == "done" and .[1][0:2] == ["aborted", "user_abort"] and .[2] == "true\n"' ;;
            called) expectation='.[0:2] == ["done", ["returned"]] and .[2] == "true\n7\n9\n"' ;;
            looping) expectation='.[0] == "timeout" and .[1] == "true\n"' ;;
            call_kill) expectation='.[0:2] == ["done", ["returned"]] and .[2] == "true\n"' ;;
            scope_kill|loop_counter) expectation='.[0:2] == ["done", ["returned"]] and .[2] == "11\n"' ;;
        esac
        "$jaq" -e "$expectation" "$result" >/dev/null || {
            cat "$result" >&2
            fail "$name $profile source outcome"
        }
    done
    echo "bce $name: $proven proven indexes, independent validation and both numeric profiles agree"
done
