#!/bin/sh
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
goose=${1:-$root/build/goose}
semantics=${2:-$root/semantics/.lake/build/bin/goose-semantics}
cc=${3:-clang}

mkdir -p "$root/.work/tmp"
export TMPDIR=$root/.work/tmp
work=$(mktemp -d "$TMPDIR/core-bottom-block.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM

for name in sem_construction_bottom_block core_bottom_cases/elements core_bottom_cases/exit; do
    source=$here/$name.goose
    expected=$here/$name.out
    if [ "$name" = sem_construction_bottom_block ]; then
        expected=$root/test/expected/$name.out
    fi
    core=$work/program.core.json
    "$goose" --emit-core "$core" --check "$source"
    "$semantics" validate "$core" > "$work/validation.json"
    jaq -e '. == ["ok"]' "$work/validation.json" > /dev/null
    outcome='["returned"]'
    if [ "$name" = core_bottom_cases/exit ]; then outcome='["exited",7]'; fi
    for numeric in release debug; do
        "$semantics" run "$core" --numeric "$numeric" > "$work/result.json"
        jaq -e --argjson outcome "$outcome" '.[0] == "done" and .[1] == $outcome' "$work/result.json" > /dev/null
        jaq -jr '.[2] | if type == "array" then implode else . end' "$work/result.json" > "$work/core.out"
        cmp "$expected" "$work/core.out"
    done
done

if "$goose" --emit-core "$work/invalid.core.json" --check \
        "$here/core_bottom_cases/returning_void.goose" > "$work/invalid.log" 2>&1; then
    echo 'FAIL returning void expression accepted as an integer element' >&2
    exit 1
fi
rg -q 'expected a value of type i64, got void' "$work/invalid.log"
[ ! -e "$work/invalid.core.json" ]

"$goose" --standalone -o "$work/program.c" "$here/sem_construction_bottom_block.goose"
"$cc" -O0 -DGS_DEBUG=1 "$work/program.c" -o "$work/program" -lm -pthread
"$work/program" > "$work/native.out"
cmp "$root/test/expected/sem_construction_bottom_block.out" "$work/native.out"

echo 'ok bottom expressions retain exit behavior in typed aggregates'
