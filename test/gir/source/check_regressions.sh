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

check_static_root gir_static_root_global stored-reference
check_static_root gir_static_root_holder struct-whole-const

echo "GIR static-root regressions passed"
