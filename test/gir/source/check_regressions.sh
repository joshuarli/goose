#!/bin/sh
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
goose=${1:-$root/build/goose}
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

check_static_root gir_static_root_global stored-reference
check_static_root gir_static_root_holder struct-whole-const
check_named_bitnot

echo "GIR static-root and named-bitnot regressions passed"
