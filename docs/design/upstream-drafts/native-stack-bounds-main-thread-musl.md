fix(runtime): bound the main thread's native stack by its limit

## What

On musl, a native stack overflow on the main thread dies of SIGSEGV instead of printing `goose runtime error: native call stack overflow` and exiting 1, natively and under `--jit`. The `native_stack_overflow` and `render_reference_cycle` fixtures fail for this reason at `-O0` and `-O2`.

## Why

Spec §9.3 makes native stack exhaustion a safe abort with a diagnostic. The fault handler recognizes the overflow by the range `pthread_getattr_np` reports for the thread's stack. musl reports only what the kernel has mapped so far for the main thread (observed: 126976 bytes against an 8 MiB limit), where glibc reports the `RLIMIT_STACK` extent. The overflow fault lands about 8 MiB below that range, so the handler hands it to the default action.

## How

The main thread's range is widened to the `RLIMIT_STACK` limit when the libc reports less. Workers have a fixed allocation and are unchanged. `src/runtime_inline.h` is regenerated; `docs/implementation.md` notes the widening. The two existing fixtures are the regression test on musl; they already pass on glibc, so no fixture is added.

## Testing

Verified locally on Alpine edge (musl, x86_64): both fixtures fail before the fix (status 139) and pass after (status 1, diagnostic on stderr), as native C at `-O0 -DGS_DEBUG=1` and under `--jit`, built with Clang 23.1.3 and GCC 15.2.0. `python3 test/run_tests.py --exe build/goose --profile baseline --cc native --require-clang` passes in full with the fix on the same host. On Debian sid (glibc 2.43) with Clang 23.1.3 and GCC 16.2.0 the fixtures pass both before and after, so behavior there is unchanged. GCC 16.2.0 on musl was not run: no image offered it.

Compiler: Clang/CMake Debug build of the compiler. Host kernel (`uname -srvm`):

```text
Linux 7.2.9-2-stable #3-Alpine SMP PREEMPT_DYNAMIC 2026-10-06 20:49:35 x86_64
```

Performance: perf gate deferred: host busy. The change runs once per thread start and adds one `getrlimit` call on the main thread; no `test/goose_in_goose` before/after measurement has been made yet.

## Reproduction

```sh
docker build --progress=plain -t goose-musl-stack-repro .
docker run --rm goose-musl-stack-repro
```

```dockerfile
FROM alpine:edge@sha256:020dfcbaaf4cc1078bf2d9c7ba31a8466e334061dcd2f248001d68f79e52c000
RUN apk add --no-cache clang gcc g++ musl-dev cmake samurai python3 linux-headers
WORKDIR /repro
ADD https://codeload.github.com/aardappel/goose/zip/1cfe4b6bde2c52b97a61a268e78361caa3804fd4 base.zip
ADD https://codeload.github.com/aardappel/goose/zip/FIX_COMMIT_PLACEHOLDER fix.zip
RUN for rev in base fix; do \
    cmake -E tar xf "$rev.zip" && mv goose-* "$rev" && rm "$rev.zip" || exit 1; done
RUN for rev in base fix; do \
    cmake -S "$rev" -B "$rev/build" -G Ninja -DCMAKE_BUILD_TYPE=Debug \
      -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ \
      -DGOOSE_LIBTCC=ON -DGOOSE_GFX=OFF -DGOOSE_AUDIO=OFF -DGOOSE_PHYSICS=OFF -DGOOSE_UI=OFF && \
    cmake --build "$rev/build" --parallel 8 || exit 1; done
RUN cat > verify.sh <<'SH'
set -eu
ulimit -c 0
msg='goose runtime error: native call stack overflow'
clang --version | head -n 1
gcc --version | head -n 1
apk info -v musl
uname -srvm
for cc in clang gcc; do
  for t in native_stack_overflow render_reference_cycle; do
    src=fix/test/runtime/$t.goose
    for rev in base fix; do
      $rev/build/goose --standalone $src -o $rev-$t.c > /dev/null
      $cc -O0 -DGS_DEBUG=1 $rev-$t.c -o $rev-$t -lm -pthread
      if ./$rev-$t > /dev/null 2> $rev-$t.err; then s=0; else s=$?; fi
      jit=$rev/build/goose
      if $jit --jit $src > /dev/null 2> $rev-$t.jit.err; then js=0; else js=$?; fi
      echo "$cc $rev $t: native status $s, jit status $js"
      if [ $rev = base ]; then
        ! grep -q "$msg" $rev-$t.err && [ "$s" -eq 139 ] || { echo "unexpected baseline"; exit 1; }
        [ "$js" -eq 139 ] || { echo "unexpected baseline jit"; exit 1; }
      else
        [ "$s" -eq 1 ] && grep -q "$msg" $rev-$t.err || { echo "fix native fails"; exit 1; }
        [ "$js" -eq 1 ] && grep -q "$msg" $rev-$t.jit.err || { echo "fix jit fails"; exit 1; }
      fi
    done
  done
done
echo 'PASS: baseline dies of SIGSEGV (139); fixed build reports the overflow and exits 1, natively and under JIT.'
SH
CMD ["sh", "verify.sh"]
```
