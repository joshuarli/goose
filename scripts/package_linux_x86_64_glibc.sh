#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
    printf '%s\n' "This package must be built on Linux x86_64." >&2
    exit 1
fi
if ! command -v gcc >/dev/null 2>&1 || ! command -v g++ >/dev/null 2>&1; then
    printf '%s\n' "GCC and G++ are required to build the glibc target." >&2
    exit 1
fi

glibc_version="$(getconf GNU_LIBC_VERSION 2>/dev/null || true)"
if [[ "$glibc_version" != glibc\ * ]]; then
    printf '%s\n' "A GNU glibc build environment is required." >&2
    exit 1
fi

gcc_version="$(gcc -dumpfullversion -dumpversion)"
gxx_version="$(g++ -dumpfullversion -dumpversion)"
if [[ "$gcc_version" != "$gxx_version" ]]; then
    printf 'GCC and G++ versions differ: %s and %s.\n' "$gcc_version" "$gxx_version" >&2
    exit 1
fi

build_dir="$repo_root/build/toolchain-linux-x86_64-glibc"
stage_dir="$build_dir/package/goose-linux-x86_64-glibc"
dist_dir="$repo_root/dist"
archive="$dist_dir/goose-linux-x86_64-glibc.zip"

CC=gcc CXX=g++ cmake -S "$repo_root" -B "$build_dir" \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_C_COMPILER=gcc \
    -DCMAKE_CXX_COMPILER=g++ \
    -DGOOSE_BUILTIN_LIBS=
cmake --build "$build_dir" --config Release

if ! readelf -l "$build_dir/goose" | grep -q 'INTERP'; then
    printf '%s\n' "The Goose executable has no dynamic ELF interpreter; expected a glibc-linked binary." >&2
    exit 1
fi

rm -rf "$stage_dir"
mkdir -p "$stage_dir/bin"
cp "$build_dir/goose" "$stage_dir/bin/goose"
cp -R "$build_dir/tcclib" "$stage_dir/bin/tcclib"
cp -R "$repo_root/stdlib" "$stage_dir/stdlib"
cp "$repo_root/LICENSE" "$stage_dir/LICENSE"

cat > "$stage_dir/README.txt" <<EOF
Goose compiler for Linux x86-64 (glibc)

Built with GCC $gcc_version against $glibc_version. This dynamically linked
package requires compatible glibc and GNU C++ runtime libraries on the host.
TinyCC support files are in bin/tcclib, so JIT execution is supported.
No optional native packages are bundled in this build.

Run a Goose program through the JIT with:
  bin/goose path/to/program.goose

Generate and compile a standalone program with:
  bin/goose --standalone -o program.c path/to/program.goose
  cc -O2 program.c -o program -lm -pthread
  ./program

Compiling generated C still requires a C compiler for the target system.
EOF

git_revision="$(git -C "$repo_root" rev-parse --short HEAD)"
cat > "$stage_dir/build-info.txt" <<EOF
Goose revision: $git_revision
Target: x86_64-linux-glibc
Compiler: GCC $gcc_version
Libc: $glibc_version
EOF

mkdir -p "$dist_dir"
rm -f "$archive"
(cd "$build_dir/package" && zip -qr "$archive" goose-linux-x86_64-glibc)
printf 'Created %s\n' "$archive"
