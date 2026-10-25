#!/bin/sh
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
goose=${1:-$root/build/goose}
jaq=${JAQ:-jaq}
work=$root/.work/tmp/gir-source-regressions
mkdir -p "$work" "$root/.work/tmp"
TMPDIR=$root/.work/tmp
export TMPDIR

fail() {
    echo "FAIL $*" >&2
    exit 1
}

has_unit_files() {
    [ -d "$1" ] && [ -n "$(find "$1" -type f -size +0c -print -quit)" ]
}

no_unit_files() {
    [ ! -d "$1" ] || [ -z "$(find "$1" -type f -print -quit)" ]
}

check_static_root() {
    name=$1
    feature=$2
    source=$here/$name.goose
    units=$work/$name-units
    rm -rf "$units"
    if "$goose" -O0 --pipeline gir --emit-units "$units" "$source" \
        >"$work/$name.out" 2>"$work/$name.err"; then
        has_unit_files "$units" || fail "$name succeeded without publishing units"
        return
    fi
    rg -F "unsupported in pipeline gir: $feature" "$work/$name.err" >/dev/null || {
        cat "$work/$name.out" "$work/$name.err" >&2
        fail "$name failed without a named GIR unsupported diagnostic"
    }
    no_unit_files "$units" || fail "$name published partial units after rejection"
}

check_named_bitnot() {
    name=gir_named_bitnot
    source=$here/$name.goose
    for opt in 0 2; do
        if ! "$goose" "-O$opt" --pipeline gir --jit -DGS_DEBUG=1 "$source" \
            >"$work/$name-O$opt.out" 2>"$work/$name-O$opt.err"; then
            cat "$work/$name-O$opt.out" "$work/$name-O$opt.err" >&2
            fail "$name failed under GIR debug O$opt"
        fi
        [ "$(tail -n 1 "$work/$name-O$opt.out")" = 3 ] || {
            cat "$work/$name-O$opt.out" >&2
            fail "$name did not print 3 under GIR debug O$opt"
        }
    done
}

check_named_result_later_operand() {
    name=gir_named_result_later_operand
    source=$here/$name.goose
    core=$work/$name.core
    for opt in 0 2; do
        if ! "$goose" "-O$opt" --pipeline gir --jit -DGS_DEBUG=1 "$source" \
            >"$work/$name-O$opt.out" 2>"$work/$name-O$opt.err"; then
            cat "$work/$name-O$opt.out" "$work/$name-O$opt.err" >&2
            fail "$name failed under GIR debug O$opt"
        fi
        [ "$(tail -n 1 "$work/$name-O$opt.out")" = '[1, 2] [9]' ] || {
            cat "$work/$name-O$opt.out" >&2
            fail "$name did not preserve the first result under GIR debug O$opt"
        }
    done

    rm -f "$core"
    if ! "$goose" --emit-core "$core" --check "$source" \
        >"$work/$name-core.out" 2>"$work/$name-core.err"; then
        cat "$work/$name-core.out" "$work/$name-core.err" >&2
        fail "$name Core export failed"
    fi
    "$jaq" -e '.[8][] | select(.[0] == "impl" and .[1] == "pair") | .[3][0][3] == [] and .[3][1][3] == []' \
        "$core" >/dev/null || fail "$name Core export retained a named-local result"
}

check_fixed_append() (
    name=$1
    profile=$2
    source=$root/test/semantics/$name.goose
    for opt in 0 2; do
        core=$work/$name-O$opt.core.json
        cfile=$work/$name-O$opt.c
        program=$work/$name-O$opt
        if ! "$goose" "-O$opt" --pipeline gir --standalone --emit-core "$core" \
            -o "$cfile" "$source" >"$work/$name-O$opt.export.out" 2>"$work/$name-O$opt.export.err"; then
            cat "$work/$name-O$opt.export.err" >&2
            fail "$name failed under GIR O$opt"
        fi
        "$jaq" -e --arg profile "$profile" '.[2] == $profile' "$core" >/dev/null ||
            fail "$name changed its semantic profile"
        clang "-O$opt" -DGS_DEBUG=1 "$cfile" -lm -pthread -o "$program"
        "$program" >"$work/$name-O$opt.out"
        cmp "$root/test/expected/$name.out" "$work/$name-O$opt.out"
    done
)

check_fixed_append sem_core_pilot_capture_grow core-pilot
check_fixed_append sem_core_shrink_owner_ops core-shrink
check_fixed_append sem_mem06_limited_fixed_array_reuse core-shrink

check_refined_integer_boundary() (
    for name in bound_type_abort index_type_abort; do
        source=$root/test/codegen/$name.goose
        for debug in 0 1; do
            if "$goose" --pipeline legacy --jit "-DGS_DEBUG=$debug" "$source" \
                >"$work/$name-legacy-$debug.out" 2>"$work/$name-legacy-$debug.err"; then
                fail "$name did not abort under the legacy pipeline"
            fi
            rg -F -f "$root/test/expected/$name.stderr" "$work/$name-legacy-$debug.err" >/dev/null ||
                fail "$name lost its legacy bounds diagnostic"
            for pipeline in core gir; do
                artifact=$work/$name-$pipeline-$debug
                rm -f "$artifact.core" "$artifact.high" "$artifact.low"
                rm -rf "$artifact-units"
                if [ "$pipeline" = core ]; then
                    set -- --check
                    marker='unsupported in core-pilot: refined-integer'
                else
                    set -- --pipeline gir --emit-gir-high "$artifact.high" \
                        --emit-gir-low "$artifact.low" --emit-units "$artifact-units"
                    marker='unsupported in pipeline gir: refined-integer'
                fi
                if "$goose" "-DGS_DEBUG=$debug" --emit-core "$artifact.core" "$@" "$source" \
                    >"$artifact.out" 2>"$artifact.err"; then
                    fail "$name lost its refined integer constraint under $pipeline"
                fi
                rg -F "$marker" "$artifact.err" >/dev/null || {
                    cat "$artifact.out" "$artifact.err" >&2
                    fail "$name failed without its refined integer unsupported diagnostic"
                }
                [ ! -e "$artifact.core" ] && [ ! -e "$artifact.high" ] && [ ! -e "$artifact.low" ] ||
                    fail "$name published an artifact after rejection"
                no_unit_files "$artifact-units" || fail "$name published partial units after rejection"
            done
        done
    done
    name=sem_num06_casts_in_range_debug
    if ! "$goose" --pipeline gir --jit -DGS_DEBUG=1 "$root/test/semantics/$name.goose" \
        >"$work/$name.out" 2>"$work/$name.err"; then
        cat "$work/$name.out" "$work/$name.err" >&2
        fail "ordinary integer casts failed under GIR"
    fi
    cmp "$root/test/expected/$name.out" "$work/$name.out"
)

check_refined_integer_boundary
check_static_root gir_static_root_global stored-reference
check_static_root gir_static_root_holder struct-whole-const
check_named_bitnot
check_named_result_later_operand

echo "GIR static-root, named-bitnot, and named-result regressions passed"
