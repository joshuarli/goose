#!/bin/sh
# A wrong lowering is caught: sampling a view after the index expression instead
# of before it.
#
#   mutation.sh [TOOL]
#
# In the lowering of sampled_extent, `short[grow_and_index(short)]` takes the
# view of `short`, then calls the function that grows `short` and returns 1,
# then checks the index against the view's length (1) and aborts. The mutation
# moves the `array.snapshot` after the call, so the view has the grown length
# (2) and the index is accepted. The mutated module still passes `gir-validate`,
# and `agree` reports that its run differs from Core's (status 6).
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
tool=${1:-$root/semantics/.lake/build/bin/goose-semantics}
work=$root/.work/tmp/gir-golden
mkdir -p "$work"
mutated=$work/sampled_extent.mutated.json

# In function 0, block 0: move the snapshot that the index uses to just before the index.
jaq -c '.[6][0][6][0][2] |= (
  . as $a
  | ($a | map(.[0] == "i_snap" and .[1] == 23) | index(true)) as $s
  | ($a | map(.[0] == "i_index" and .[2] == 23) | index(true)) as $x
  | $a[:$s] + $a[$s + 1:$x] + [$a[$s]] + $a[$x:])' \
    "$here/sampled_extent.gir-h.json" > "$mutated"

cmp -s "$mutated" "$here/sampled_extent.gir-h.json" && { echo "FAIL the mutation changed nothing" >&2; exit 1; }
[ "$("$tool" gir-validate "$mutated")" = '["ok"]' ] || { echo "FAIL the mutated module is rejected" >&2; exit 1; }

set +e
out=$("$tool" agree "$root/test/semantics/golden/sampled_extent.core.json" "$mutated")
status=$?
set -e
case $out in
    '["disagree",'*) ;;
    *) echo "FAIL expected disagree, got $out" >&2; exit 1 ;;
esac
[ "$status" -eq 6 ] || { echo "FAIL exit status $status, expected 6" >&2; exit 1; }
echo "mutation caught: $out"
