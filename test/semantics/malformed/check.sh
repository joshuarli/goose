#!/bin/sh
# Check the malformed and rejected Core decoder fixtures against goose-semantics.
#
#   check.sh [TOOL]
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
tool=${1:-$root/semantics/.lake/build/bin/goose-semantics}
tab=$(printf '\t')

while IFS="$tab" read -r file expected; do
    set +e
    actual=$("$tool" validate "$here/$file")
    code=$?
    set -e
    case $expected in
        '["ok"]'*) want=0 ;;
        '["malformed"'*) want=2 ;;
        '["rejected"'*) want=5 ;;
        *) echo "FAIL $file: unrecognized expectation" >&2; exit 1 ;;
    esac
    case $expected in
        '["rejected",'*']')
            prefix=${expected%]}
            case $actual in
                "$expected"|"$prefix",*]) ;;
                *) echo "FAIL $file: got $actual" >&2; exit 1 ;;
            esac ;;
        *) [ "$actual" = "$expected" ] || { echo "FAIL $file: got $actual" >&2; exit 1; } ;;
    esac
    [ "$code" -eq "$want" ] || { echo "FAIL $file: exit status $code, expected $want" >&2; exit 1; }
done < "$here/INDEX"

for f in "$here"/*.json; do
    grep -q "^$(basename "$f")$tab" "$here/INDEX" || {
        echo "FAIL $(basename "$f") is not in INDEX" >&2
        exit 1
    }
done

# Keep the boundary input generated so the repository does not carry a 64 MiB fixture.
work=$root/.work/tmp/malformed-input.$$
mkdir -p "$work"
trap 'rm -rf "$work"' EXIT HUP INT TERM
head -c 67108865 /dev/zero > "$work/oversize.json"
expected='["malformed","input of 67108865 bytes exceeds 67108864"]'
for command in validate gir-validate; do
    set +e
    actual=$("$tool" "$command" "$work/oversize.json")
    code=$?
    set -e
    [ "$actual" = "$expected" ] || {
        echo "FAIL $command oversize input: got $actual" >&2
        exit 1
    }
    [ "$code" -eq 2 ] || {
        echo "FAIL $command oversize input: exit status $code, expected 2" >&2
        exit 1
    }
done

echo "malformed: $(wc -l < "$here/INDEX") Core modules and both oversize decoders ok"
