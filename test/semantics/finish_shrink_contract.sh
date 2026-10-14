#!/bin/sh
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
workspace=$(cd "$root/../../.." && pwd)
goose=${1:-$workspace/.work/build/debug/goose}
semantics=${2:-$workspace/.work/wt/verify/semantics/.lake/build/bin/goose-semantics}
clang=${3:-${CLANG:-clang}}
jaq=${JAQ:-jaq}

[ -x "$goose" ] || { echo "missing Goose compiler: $goose" >&2; exit 2; }
[ -x "$semantics" ] || { echo "missing goose-semantics: $semantics" >&2; exit 2; }
command -v "$clang" >/dev/null 2>&1 || { echo "missing Clang executable: $clang" >&2; exit 2; }
command -v "$jaq" >/dev/null 2>&1 || { echo "missing jaq executable: $jaq" >&2; exit 2; }

workroot=$root/.work/tmp
mkdir -p "$workroot"
export TMPDIR=$workroot
work=$(mktemp -d "$workroot/finish-shrink.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM

python3 "$here/run_tests.py" --goose "$goose" --semantics "$semantics" \
    --pipeline gir --cc "$clang" --jobs 1 \
    --case sem_finish_shrink_grow_owner_scalar \
    --case sem_finish_shrink_limited_packed_reuse \
    --case sem_finish_shrink_growshrink_reference_replace \
    --case sem_finish_shrink_limited_packed_capacity_order

validate_indexed_fixtures() {
    directory=$1
    index=$2
    command=$3
    tab=$(printf '\t')
    found=0

    while IFS="$tab" read -r file expected; do
        case $file in
            finish_shrink_*.json) ;;
            *) continue ;;
        esac
        found=$((found + 1))
        module=$directory/$file
        output=$work/$file.out
        log=$work/$file.log
        if "$semantics" "$command" "$module" >"$output" 2>"$log"; then
            status=0
        else
            status=$?
        fi
        case $expected in
            '["malformed"'*) want=2 ;;
            '["rejected"'*) want=5 ;;
            *) echo "FAIL $file: invalid indexed expectation" >&2; exit 1 ;;
        esac
        actual=$(cat "$output")
        [ "$actual" = "$expected" ] && [ "$status" -eq "$want" ] || {
            echo "FAIL $file: got $actual (exit $status), expected $expected (exit $want)" >&2
            cat "$log" >&2
            exit 1
        }
    done < "$index"

    [ "$found" -gt 0 ] || { echo "FAIL $index: no finish-shrink fixtures" >&2; exit 1; }
    for module in "$directory"/finish_shrink_*.json; do
        [ -f "$module" ] || continue
        file=${module##*/}
        rg -Fq "$file$tab" "$index" || {
            echo "FAIL $file: missing index entry" >&2
            exit 1
        }
    done
}

validate_indexed_fixtures "$root/test/semantics/malformed" \
    "$root/test/semantics/malformed/INDEX" validate
validate_indexed_fixtures "$root/test/gir/invalid" \
    "$root/test/gir/invalid/INDEX" gir-validate

limited_source=$here/sem_finish_shrink_limited_packed_reuse.goose
"$goose" --emit-core "$work/limited.core.json" --emit-gir-high "$work/limited.high.json" \
    --emit-gir-low "$work/limited.low.json" --check "$limited_source" >"$work/export.log" 2>&1
"$jaq" -e '
    [.[6][] | select(.[1] == "clear_values")] as $clear |
    ($clear | length) == 1 and
    ([ $clear[0][7][] | .[2][] | .[0] ] as $ops |
        ([ $ops[] | select(. == "l_release" or . == "l_bump" or . == "l_move") ] | length) == 0 and
        ([ $ops[] | select(. == "l_copy") ] | length) == 1)
' "$work/limited.low.json" >/dev/null

"$goose" --pipeline gir --standalone -o "$work/limited.c" "$limited_source" \
    >"$work/pipeline.log" 2>&1
"$clang" -O0 -fsanitize=alignment -fno-sanitize-recover=alignment \
    "$work/limited.c" -lm -pthread -o "$work/limited-alignment" \
    >"$work/clang.log" 2>&1
if "$work/limited-alignment" >"$work/alignment.out" 2>"$work/alignment.err"; then
    status=0
else
    status=$?
fi
[ "$status" -eq 0 ] && [ ! -s "$work/alignment.err" ] || {
    echo "FAIL limited packed access under alignment sanitizer" >&2
    cat "$work/alignment.err" >&2
    exit 1
}
cmp "$root/test/expected/sem_finish_shrink_limited_packed_reuse.out" \
    "$work/alignment.out"

echo "finish-shrink: source/Core/GIR/native cases, decoder fixtures and packed alignment ok"
