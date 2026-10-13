#!/bin/sh
# Check every line of INDEX against the reference tool.
#
#   check.sh [TOOL]
#
# A line is a module file and the line `gir-validate` prints for it. The exit
# status must be 0 for ok, 2 for malformed and 5 for rejected. Each module
# differs from `gir_valid_base.json` in one thing, so a module that fails a
# later check than its name says would show an earlier unrelated code instead.
# `gir_accepted_*` modules pass the validator and are checked by running them.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
tool=${1:-$root/semantics/.lake/build/bin/goose-semantics}
status=0

while IFS='	' read -r file expected; do
    set +e
    actual=$("$tool" gir-validate "$here/$file")
    code=$?
    set -e
    case $expected in
        '["ok"]'*) want=0 ;;
        '["malformed"'*) want=2 ;;
        '["rejected"'*) want=5 ;;
        *) echo "FAIL $file: unrecognized expectation" >&2; status=1; continue ;;
    esac
    case $file in
        gir_rejected_v*)
            c=${file#gir_rejected_v}
            c=${c%%_*}
            case $expected in
                *"\"GIR-V$c\""*) ;;
                *) echo "FAIL $file: the expectation does not name GIR-V$c" >&2; status=1 ;;
            esac ;;
    esac
    [ "$actual" = "$expected" ] || { echo "FAIL $file: got $actual" >&2; status=1; }
    [ "$code" -eq "$want" ] || { echo "FAIL $file: exit status $code, expected $want" >&2; status=1; }
done < "$here/INDEX"

# Keep the nesting boundary input generated so the repository does not carry
# another malformed JSON fixture.
work=$root/.work/tmp/gir-invalid.$$
mkdir -p "$work"
trap 'rm -rf "$work"' EXIT HUP INT TERM
awk 'BEGIN { for (i = 0; i < 257; i++) printf "["; for (i = 0; i < 257; i++) printf "]"; print "" }' > "$work/excessive_nesting.json"
set +e
actual=$("$tool" gir-validate "$work/excessive_nesting.json")
code=$?
set -e
expected='["malformed","byte 256: nesting deeper than 256"]'
[ "$actual" = "$expected" ] || {
    echo "FAIL gir-validate excessive nesting: got $actual" >&2
    status=1
}
[ "$code" -eq 2 ] || {
    echo "FAIL gir-validate excessive nesting: exit status $code, expected 2" >&2
    status=1
}

# This is valid JSON at the supported nesting limit; the GIR schema rejects its
# top-level value after the decoder has parsed it.
awk 'BEGIN { for (i = 0; i < 256; i++) printf "["; printf "0"; for (i = 0; i < 256; i++) printf "]"; print "" }' > "$work/within_limit.json"
set +e
actual=$("$tool" gir-validate "$work/within_limit.json")
code=$?
set -e
[ "$code" -eq 2 ] && [ "$actual" != "$expected" ] || {
    echo "FAIL gir-validate within-limit nesting: got $actual ($code)" >&2
    status=1
}

# A module can be accepted and still fault: acceptance says nothing about reference lifetime.
set +e
out=$("$tool" gir-run "$here/gir_accepted_dangling_reference.json")
code=$?
set -e
[ "$out" = '["fault","dangling_root"]' ] && [ "$code" -eq 4 ] ||
    { echo "FAIL gir_accepted_dangling_reference.json: run gave $out ($code)" >&2; status=1; }

set +e
out=$("$tool" gir-run "$here/gir_accepted_unreachable.json")
code=$?
set -e
[ "$out" = '["done",["exited",7],""]' ] && [ "$code" -eq 0 ] ||
    { echo "FAIL gir_accepted_unreachable.json: run gave $out ($code)" >&2; status=1; }

for f in "$here"/*.json; do
    grep -q "^$(basename "$f")	" "$here/INDEX" || { echo "FAIL $(basename "$f") is not in INDEX" >&2; status=1; }
done

[ "$status" -eq 0 ] && echo "invalid: $(wc -l < "$here/INDEX") modules and excessive nesting ok"
exit "$status"
