#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
if [[ "$(uname -s)" != Darwin || "$(uname -m)" != arm64 ]]; then
    printf '%s\n' "This package must be built on macOS arm64." >&2
    exit 1
fi

if ! command -v brew >/dev/null 2>&1; then
    printf '%s\n' "Homebrew is required to install LLVM 23." >&2
    exit 1
fi

# Use the current Homebrew bottle so the packaged compiler is built by the
# latest LLVM 23 release available from Homebrew at packaging time.
brew install llvm
brew upgrade llvm
llvm_prefix="$(brew --prefix llvm)"
clang="$llvm_prefix/bin/clang"
clangxx="$llvm_prefix/bin/clang++"
llvm_config="$llvm_prefix/bin/llvm-config"
clang_version="$("$clangxx" --version | sed -n '1s/.*version \([0-9][0-9.]*\).*/\1/p')"
llvm_version="$("$llvm_config" --version)"
if [[ "$clang_version" != 23.* || "$llvm_version" != "$clang_version" ]]; then
    printf 'Expected matching Homebrew LLVM/Clang 23, found LLVM %s and Clang %s.\n' \
        "${llvm_version:-unknown}" "${clang_version:-unknown}" >&2
    exit 1
fi

git -C "$repo_root" submodule update --init third_party/tinycc

build_dir="$repo_root/build/toolchain-macos-aarch64"
stage_dir="$build_dir/package/goose-macos-aarch64"
dist_dir="$repo_root/dist"
archive="$dist_dir/goose-macos-aarch64.zip"

CC="$clang" CXX="$clangxx" cmake -S "$repo_root" -B "$build_dir" \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_C_COMPILER="$clang" \
    -DCMAKE_CXX_COMPILER="$clangxx" \
    -DGOOSE_GFX=OFF -DGOOSE_AUDIO=OFF -DGOOSE_PHYSICS=OFF -DGOOSE_UI=OFF
cmake --build "$build_dir" --config Release

rm -rf "$stage_dir"
mkdir -p "$stage_dir/bin"
cp "$build_dir/goose" "$stage_dir/bin/goose"
cp -R "$build_dir/tcclib" "$stage_dir/bin/tcclib"
cp -R "$repo_root/stdlib" "$stage_dir/stdlib"
cp "$repo_root/LICENSE" "$stage_dir/LICENSE"

cat > "$stage_dir/README.txt" <<EOF
Goose compiler for macOS arm64

Built with Homebrew LLVM/Clang $clang_version.
The compiler and standard library are bundled together. TinyCC support files
are in bin/tcclib for in-process execution with --jit.
The native audio, graphics, physics, and ui modules are not enabled in this
build.

Run a source file with:
  bin/goose path/to/program.goose

Generate C with:
  bin/goose -o program.c path/to/program.goose

This package does not include a native C compiler. Install Xcode Command Line
Tools or Homebrew LLVM to compile generated C programs.
EOF

git_revision="$(git -C "$repo_root" rev-parse --short HEAD)"
cat > "$stage_dir/build-info.txt" <<EOF
Goose revision: $git_revision
Target: macOS arm64
Compiler: Homebrew LLVM/Clang $clang_version
LLVM: $llvm_version
EOF

mkdir -p "$dist_dir"
rm -f "$archive"
(cd "$build_dir/package" && zip -qr "$archive" goose-macos-aarch64)
printf 'Created %s\n' "$archive"
