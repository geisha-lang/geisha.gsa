#!/bin/sh
# Package relocatable Geisha compiler release tarball(s) into $DIST_DIR.
set -eu

VERSION="${VERSION:-dev}"
DIST_DIR="${DIST_DIR:-dist}"
BUILD_DIR="${BUILD_DIR:-build}"
CC="${CC:-clang}"

UNAME_S="$(uname -s)"
UNAME_M="$(uname -m)"

case "$UNAME_S" in
    Darwin) OS_NAME="darwin" ;;
    Linux)  OS_NAME="linux" ;;
    *)      OS_NAME="$(echo "$UNAME_S" | tr '[:upper:]' '[:lower:]')" ;;
esac

case "$UNAME_M" in
    arm64|aarch64) ARCH_NAME="arm64" ;;
    x86_64|amd64)  ARCH_NAME="x86_64" ;;
    *)             ARCH_NAME="$UNAME_M" ;;
esac

sha256_file() {
    if command -v sha256sum >/dev/null 2>&1; then
        sha256sum "$1" | awk '{print $1}'
    else
        shasum -a 256 "$1" | awk '{print $1}'
    fi
}

package_one() {
    pkg_os="$1"
    pkg_arch="$2"
    bin_path="$3"
    rt_path="$4"

    stem="geisha-${VERSION}-${pkg_os}-${pkg_arch}"
    stage_root="$DIST_DIR/$stem"
    rm -rf "$stage_root"
    mkdir -p "$stage_root/bin" "$stage_root/lib"

    cp "$bin_path" "$stage_root/bin/geisha"
    chmod 0755 "$stage_root/bin/geisha"
    cp "$rt_path" "$stage_root/lib/libgeisha_runtime.a"
    if [ -f "$BUILD_DIR/wasm_rt.o" ]; then
        cp "$BUILD_DIR/wasm_rt.o" "$stage_root/lib/wasm_rt.o"
    fi
    if [ -f "tools/geisha_lldb.py" ]; then
        cp "tools/geisha_lldb.py" "$stage_root/lib/geisha_lldb.py"
    fi
    cp README.md "$stage_root/README.md"

    tarball="$DIST_DIR/${stem}.tar.gz"
    tar -C "$DIST_DIR" -czf "$tarball" "$stem"
    rm -rf "$stage_root"

    sum="$(sha256_file "$tarball")"
    printf "%s  %s\n" "$sum" "${stem}.tar.gz" > "${tarball}.sha256"
    echo "Packaged $tarball ($sum)"
}

mkdir -p "$DIST_DIR"
package_one "$OS_NAME" "$ARCH_NAME" "$BUILD_DIR/geisha3" "$BUILD_DIR/libgeisha_runtime.a"

# Optional cross-packaging of darwin-x86_64 on Apple Silicon macOS using the Universal SDK
if [ "${PACKAGE_DARWIN_X86_64:-0}" = "1" ] && [ "$OS_NAME" = "darwin" ] && [ "$ARCH_NAME" = "arm64" ]; then
    X64_DIR="$BUILD_DIR/darwin_x86_64"
    rm -rf "$X64_DIR"
    mkdir -p "$X64_DIR"

    MACOSX_DEPLOYMENT_TARGET=14.0 "$CC" -target x86_64-apple-macosx14.0 -O2 -Wall -Wextra -Iruntime/include -c runtime/base.c -o "$X64_DIR/base.o"
    MACOSX_DEPLOYMENT_TARGET=14.0 "$CC" -target x86_64-apple-macosx14.0 -O2 -Wall -Wextra -Iruntime/include -c runtime/gs_sys.c -o "$X64_DIR/gs_sys.o"
    MACOSX_DEPLOYMENT_TARGET=14.0 "$CC" -target x86_64-apple-macosx14.0 -O2 -Wall -Wextra -Iruntime/include -c runtime/runtime/gc_bitmap.c -o "$X64_DIR/gc_bitmap.o"
    MACOSX_DEPLOYMENT_TARGET=14.0 "$CC" -target x86_64-apple-macosx14.0 -O2 -Wall -Wextra -Iruntime/include -c runtime/runtime/gs_conc.c -o "$X64_DIR/gs_conc.o"
    ar rcs "$X64_DIR/libgeisha_runtime.a" "$X64_DIR/base.o" "$X64_DIR/gs_sys.o" "$X64_DIR/gc_bitmap.o" "$X64_DIR/gs_conc.o"

    MACOSX_DEPLOYMENT_TARGET=14.0 "$CC" -target x86_64-apple-macosx14.0 -O2 -Wno-override-module -pthread -x ir "$BUILD_DIR/stage3.ll" -x none "$X64_DIR/libgeisha_runtime.a" -o "$X64_DIR/geisha"
    package_one "darwin" "x86_64" "$X64_DIR/geisha" "$X64_DIR/libgeisha_runtime.a"
    rm -rf "$X64_DIR"
fi
