#!/bin/sh
# Check every line of INDEX against the reference tool.
#
#   check.sh [TOOL]
#
# A line is a module file and the line `gir-validate` prints for it. The exit
# status must be 0 for ok, 2 for malformed and 5 for rejected. Each module
# differs from `gir_valid_base.json` in one thing, so a module that fails a
# later check than its name says would show an earlier unrelated code instead.
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

for f in "$here"/*.json; do
    grep -q "^$(basename "$f")	" "$here/INDEX" || { echo "FAIL $(basename "$f") is not in INDEX" >&2; status=1; }
done

[ "$status" -eq 0 ] && echo "invalid: $(wc -l < "$here/INDEX") modules ok"
exit "$status"
