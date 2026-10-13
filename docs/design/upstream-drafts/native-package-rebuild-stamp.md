# fix(build): rebuild a package's native part when its C source changes

## What

`goose build` and `goose run` now rebuild a program's or path package's native C when one of its `c_sources` changes. Before, an edited C source kept its old object: the program printed the old result until the sidecar changed.

## Why

`docs/design/packages.md` says "a path package rebuilds when any of its sources is newer than its build". With libstdc++ (GCC and Clang on glibc or musl) the stamp's time field was always `0`, so only a toolchain or sidecar change could trigger a rebuild.

## How

`NewestMtime` seeded its maximum with 0 and took it over `file_time_type::time_since_epoch().count()`. libstdc++'s file clock counts from 2174, so every count is negative and 0 always won. It now compares the file times themselves and stamps the newest in nanoseconds, with no assumption about the clock's epoch or sign. `ImportVcvars` also prints a file clock count, but only as an equality key, so it is unaffected. Header tracking through `c_include` is not promised and is not part of this change.

## Testing

Verified locally: `test/native_rebuild.py` (run by `run_tests.py`) builds a program with a sidecar C source in a scratch `GOOSE_HOME`, checks that an unchanged rebuild leaves the object alone, edits the source and requires the new output. On the base it fails (`printed '1', wanted '2'`); with the fix it passes (5 repeated passes). Reproducer below: base keeps the stale result 1 and the fix prints 2, with both Clang- and GCC-built compilers, and the package C compiled by the same compiler. Compilers: `Debian clang version 23.1.3 (1)`, `gcc-16 (Debian 16.2.0-3) 16.2.0`, `ldd (Debian GLIBC 2.43-7) 2.43`, CMake Debug builds with libstdc++ (libc++ not tested). Docker host kernel (`uname -srvm`):

```text
Linux 7.2.9-2-stable #3-Alpine SMP PREEMPT_DYNAMIC 2026-10-06 20:49:35 x86_64
```

Also `python3 test/run_tests.py --profile baseline --cc native --require-clang` on a musl Alpine host (GCC 15.2.0, Clang): everything passed except `native_stack_overflow` and `render_reference_cycle`, which also fail on the base for an unrelated reason.

perf gate deferred: host busy. Owed: paired before/after `test/goose_in_goose` and warm/cold `goose build` timings against the exact base, with peak memory. The change runs once per build over a handful of `stat` calls.

## Reproduction

```sh
docker build --progress=plain -t goose-stamp-repro .
docker run --rm goose-stamp-repro
```

```dockerfile
FROM debian:sid-slim@sha256:1f11c32b03195c1b28c55e4579755659edae5c76dd76a69b4e4fb34c58fa8744
RUN apt-get update && apt-get install -y --no-install-recommends clang-23 gcc-16 g++-16 cmake ninja-build && rm -rf /var/lib/apt/lists/*
WORKDIR /repro
ADD https://codeload.github.com/aardappel/goose/zip/1cfe4b6bde2c52b97a61a268e78361caa3804fd4 base.zip
ADD https://codeload.github.com/aardappel/goose/zip/<FIX-COMMIT-SHA> fix.zip
RUN for rev in base fix; do \
    cmake -E tar xf "$rev.zip" && mv goose-* "$rev" && rm "$rev.zip" || exit 1; done
RUN for rev in base fix; do \
    cmake -S "$rev" -B "$rev/build" -G Ninja -DCMAKE_BUILD_TYPE=Debug \
      -DCMAKE_C_COMPILER=clang-23 -DCMAKE_CXX_COMPILER=clang++-23 \
      -DGOOSE_LIBTCC=OFF -DGOOSE_GFX=OFF -DGOOSE_AUDIO=OFF -DGOOSE_PHYSICS=OFF -DGOOSE_UI=OFF && \
    cmake --build "$rev/build" --parallel 2 || exit 1; done
RUN for rev in base fix; do \
    cmake -S "$rev" -B "$rev/build-gcc" -G Ninja -DCMAKE_BUILD_TYPE=Debug \
      -DCMAKE_C_COMPILER=gcc-16 -DCMAKE_CXX_COMPILER=g++-16 \
      -DGOOSE_LIBTCC=OFF -DGOOSE_GFX=OFF -DGOOSE_AUDIO=OFF -DGOOSE_PHYSICS=OFF -DGOOSE_UI=OFF && \
    cmake --build "$rev/build-gcc" --parallel 2 || exit 1; done
RUN cat > verify.sh <<'SH'
set -eu
ulimit -c 0
clang-23 --version | head -n 1
gcc-16 --version | head -n 1
ldd --version | head -n 1
uname -srvm
# Builds a program whose sidecar C returns 1, edits that C to return 2, and
# rebuilds. Prints the stamp's time field and both results.
probe() {
    goose=$1 cc=$2 dir=$3
    mkdir -p "$dir"
    printf 'extern fn answer() -> i32;\nfn main() { print(answer()); }\n' > "$dir/main.goose"
    printf 'c_sources = ["impl.c"];\n' > "$dir/main.build"
    printf 'int answer(void) { return 1; }\n' > "$dir/impl.c"
    export GOOSE_HOME="$dir/home"
    "$goose" build --cc "$cc" -o "$dir/main" "$dir/main.goose" > "$dir/b1.log" 2>&1 || { cat "$dir/b1.log" >&2; exit 1; }
    first=$("$dir/main")
    obj=$(ls "$dir"/home/build/prog/*/native/*/impl.o)
    stamp=$(stat -c %y "$obj")
    "$goose" build --cc "$cc" -o "$dir/main" "$dir/main.goose" > "$dir/b2.log" 2>&1
    [ "$(stat -c %y "$obj")" = "$stamp" ] && same=unchanged-not-rebuilt || same=unchanged-REBUILT
    printf 'int answer(void) { return 2; }\n' > "$dir/impl.c"
    touch -d 'now + 2 seconds' "$dir/impl.c"
    "$goose" build --cc "$cc" -o "$dir/main" "$dir/main.goose" > "$dir/b3.log" 2>&1
    second=$("$dir/main")
    echo "time field: $(sed -n 2p "$dir"/home/build/prog/*/native/*/stamp); first=$first; $same; after edit=$second"
    RESULT=$second
}
for t in clang gcc; do
    case $t in clang) cc=$(command -v clang-23); sfx=build;; gcc) cc=$(command -v gcc-16); sfx=build-gcc;; esac
    for rev in base fix; do
        echo "== $rev, goose and package C built with $cc"
        probe "$PWD/$rev/$sfx/goose" "$cc" "$PWD/probe-$rev-$t"
        if [ "$rev" = base ]; then
            [ "$RESULT" = 1 ] || { echo "expected the stale result 1 on base" >&2; exit 1; }
        else
            [ "$RESULT" = 2 ] || { echo "expected the rebuilt result 2 on fix" >&2; exit 1; }
        fi
    done
done
echo 'PASS: base keeps the stale object after a C edit; fix rebuilds it, with Clang and GCC.'
SH
CMD ["sh", "verify.sh"]
```
