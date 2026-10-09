#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
    printf '%s\n' "This package must be built on Linux x86_64." >&2
    exit 1
fi
if ! command -v zig >/dev/null 2>&1; then
    printf '%s\n' "Zig is required to build the static musl target." >&2
    exit 1
fi

git -C "$repo_root" submodule update --init third_party/tinycc

build_dir="$repo_root/build/toolchain-linux-x86_64-musl"
stage_dir="$build_dir/package/goose-linux-x86_64-musl"
dist_dir="$repo_root/dist"
archive="$dist_dir/goose-linux-x86_64-musl.zip"
cc_wrapper="$build_dir/zig-cc"
cxx_wrapper="$build_dir/zig-cxx"
mkdir -p "$build_dir"

cat > "$cc_wrapper" <<'EOF'
#!/usr/bin/env bash
exec zig cc -target x86_64-linux-musl -static "$@"
EOF
cat > "$cxx_wrapper" <<'EOF'
#!/usr/bin/env bash
exec zig c++ -target x86_64-linux-musl -static "$@"
EOF
chmod +x "$cc_wrapper" "$cxx_wrapper"

CC="$cc_wrapper" CXX="$cxx_wrapper" cmake -S "$repo_root" -B "$build_dir" \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_C_COMPILER="$cc_wrapper" \
    -DCMAKE_CXX_COMPILER="$cxx_wrapper" \
    -DCMAKE_C_COMPILER_TARGET=x86_64-linux-musl \
    -DCMAKE_CXX_COMPILER_TARGET=x86_64-linux-musl \
    -DCMAKE_EXE_LINKER_FLAGS=-static \
    -DGOOSE_GFX=OFF -DGOOSE_AUDIO=OFF -DGOOSE_PHYSICS=OFF -DGOOSE_UI=OFF
cmake --build "$build_dir" --config Release

if readelf -l "$build_dir/goose" | grep -q 'INTERP'; then
    printf '%s\n' "The Goose executable has a dynamic ELF interpreter; expected a static musl binary." >&2
    exit 1
fi

rm -rf "$stage_dir"
mkdir -p "$stage_dir/bin"
cp "$build_dir/goose" "$stage_dir/bin/goose"
cp -R "$build_dir/tcclib" "$stage_dir/bin/tcclib"
cp -R "$repo_root/stdlib" "$stage_dir/stdlib"
cp "$repo_root/LICENSE" "$stage_dir/LICENSE"

cat > "$stage_dir/README.txt" <<'EOF'
Goose compiler for Linux x86-64 (musl)

The compiler is statically linked against musl and can run without a system
glibc or a separately installed C++ runtime. TinyCC support files are in
bin/tcclib for in-process execution with --jit.
The native audio, graphics, physics, and ui modules are not enabled in this
build.

Run a source file with:
  bin/goose path/to/program.goose

Generate C with:
  bin/goose -o program.c path/to/program.goose

Compiling generated C still requires a C compiler for the target system.
EOF

git_revision="$(git -C "$repo_root" rev-parse --short HEAD)"
cat > "$stage_dir/build-info.txt" <<EOF
Goose revision: $git_revision
Target: x86_64-linux-musl
Compiler: Zig $(zig version)
EOF

mkdir -p "$dist_dir"
rm -f "$archive"
(cd "$build_dir/package" && zip -qr "$archive" goose-linux-x86_64-musl)
printf 'Created %s\n' "$archive"
