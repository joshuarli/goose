#!/bin/sh
# Keep future-rebind shrink rejection ahead of Core and GIR publication.
set -eu

here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
goose=${1:-$root/build/goose}

[ -x "$goose" ] || { echo "missing Goose compiler: $goose" >&2; exit 2; }

workroot=$root/.work/tmp
mkdir -p "$workroot"
export TMPDIR=$workroot
work=$(mktemp -d "$workroot/s8-mem04-07.XXXXXX")
trap 'rm -rf "$work"' EXIT HUP INT TERM

source=$here/s8_mem04_07_negative/sem_mem04_future_rebind.goose
core=$work/future-rebind.core.json
high=$work/future-rebind.gir-h.json
low=$work/future-rebind.gir-l.json
log=$work/future-rebind.log

set +e
"$goose" --emit-core "$core" --emit-gir-high "$high" --emit-gir-low "$low" \
    --check "$source" >"$log" 2>&1
status=$?
set -e

[ "$status" -eq 1 ] || {
    echo "FAIL future-rebind: expected source rejection, got exit $status" >&2
    cat "$log" >&2
    exit 1
}
case $(cat "$log") in
    *"cannot pop values while run"*"is still used: it may refer into values"*) ;;
    *)
        echo "FAIL future-rebind: missing live-view rejection" >&2
        cat "$log" >&2
        exit 1
        ;;
esac
for artifact in "$core" "$high" "$low"; do
    [ ! -e "$artifact" ] || {
        echo "FAIL future-rebind: published $artifact" >&2
        exit 1
    }
done

echo "ok future-rebind rejected before Core/GIR publication"
