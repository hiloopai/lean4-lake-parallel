#!/usr/bin/env bash
# Build the Lake overlay for the release toolchain on PATH: this checkout's Lake, compiled by that
# toolchain and linked as `src/stdlib.make.in` links the toolchain's own `libLake_shared` and `lake`.
#   build.sh WORK OUT
# WORK is a new directory: WORK/src gets the sources and WORK/pkg the built package.
# OUT gets the overlay: each toolchain Lake file whose built bytes differ, at its toolchain path.
set -euo pipefail
work=$1 out=$2
here=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
repo=$(cd -- "$here/../.." && pwd)
mkdir -p "$work/src" "$work/pkg"
cp -a "$repo/src/lake" "$repo/src/LeanExport" "$repo/src/LeanExport.lean" "$work/src/"
cp "$here/lakefile.toml" "$work/pkg/"
mkdir -p "$work/pkg/.lake/build"
cp -a "$(lean --print-prefix)/include" "$work/pkg/.lake/build/include"
cd "$work/pkg"
lake build
build=$work/pkg/.lake/build
leanc -shared -o "$build/lib/lean/libLake_shared.so" \
  -Wl,--whole-archive "$(lake query Lake:static.export)" -Wl,--no-whole-archive \
  "$(lake query LeanExport:static.export)" -Wl,-soname=libLake_shared.so \
  -lleanshared -lleanshared_2 -lleanshared_1 -lInit_shared -Wl,-rpath,'$ORIGIN/..:$ORIGIN'
mkdir -p "$build/bin"
leanc -leanshared "$(lake query +LakeMain:c.o.export)" -L"$build/lib/lean" -lLake_shared \
  -Wl,-rpath,'$ORIGIN/../lib:$ORIGIN/../lib/lean' -rdynamic \
  -lInit_shared -lleanshared_2 -lleanshared_1 -lleanshared -o "$build/bin/lake"
python3 "$here/check.py" select "$(lean --print-prefix)" "$build" "$out"
