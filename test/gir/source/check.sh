#!/bin/sh
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
goose=${1:-$root/build/goose}
jaq=${JAQ:-jaq}
work=$root/.work/tmp/gir-source-structs
mkdir -p "$work"

check_unsupported() {
    name=$1
    source=$here/$name.goose
    core=$work/$name.core
    high=$work/$name.gir-h
    low=$work/$name.gir-l
    rm -f "$core" "$high" "$low"
    if "$goose" --pipeline gir --emit-core "$core" --emit-gir-high "$high" \
        --emit-gir-low "$low" --check "$source" >"$work/$name.out" 2>"$work/$name.err"; then
        echo "FAIL $name unexpectedly exported" >&2
        exit 1
    fi
    rg -F "unsupported in pipeline gir: struct" "$work/$name.err" >/dev/null || {
        cat "$work/$name.err" >&2
        echo "FAIL $name did not report unsupported nested const elements" >&2
        exit 1
    }
    for artifact in "$core" "$high" "$low"; do
        [ ! -e "$artifact" ] || {
            echo "FAIL $name published partial artifact $artifact" >&2
            exit 1
        }
    done
}

check_unsupported nested_const_scalar
check_unsupported nested_const_struct

name=direct_const_contents
source=$here/$name.goose
core=$work/$name.core
high=$work/$name.gir-h
low=$work/$name.gir-l
rm -f "$core" "$high" "$low"
"$goose" --pipeline gir --emit-core "$core" --emit-gir-high "$high" \
    --emit-gir-low "$low" --check "$source" >"$work/$name.out" 2>"$work/$name.err"
for artifact in "$core" "$high"; do
    [ -s "$artifact" ] || {
        echo "FAIL $name did not publish $artifact" >&2
        exit 1
    }
    "$jaq" -e '.[5][0][2][0][3] == "const"' "$artifact" >/dev/null
done
[ -s "$low" ] || {
    echo "FAIL $name did not publish $low" >&2
    exit 1
}

echo "source struct export: nested element const rejected without artifacts; direct field const preserved"
