set -eu
ulimit -c 0
repo=$(CDPATH= cd -- "$(dirname -- "$0")/../.." && pwd)
compiler=$1
work=$repo/.work/units_thread_globals
mkdir -p "$work" "$repo/.work/tmp"
export TMPDIR=$repo/.work/tmp
export GOOSE_HOME=$work/home
"$compiler" build --units --standalone --include "$repo/test/scale/units_thread_globals/alignment.h" \
    -o "$work/program" "$repo/test/scale/units_thread_globals/main.goose"
"$work/program" > "$work/output"
printf 'isolated\n' > "$work/expected"
cmp "$work/expected" "$work/output"
printf 'PASS: module globals retain alignment and worker isolation in units\n'
