#!/bin/bash
#
# Patch test: build a project, apply source changes to its AIN, and verify
# that the result can be decompiled and rebuilt.

set -u

cd "$(dirname "$0")"

ROOT=../..
SYS4C="${SYS4C:-$ROOT/_build/default/bin/sys4c.exe}"
SYS4DC="${SYS4DC:-$ROOT/_build/default/bin/sys4dc.exe}"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# The native (mingw) Windows binaries can't resolve Cygwin paths like
# /tmp/...; pass them a Windows path instead.
if command -v cygpath >/dev/null 2>&1; then
	wintmp=$(cygpath -m "$tmp")
else
	wintmp=$tmp
fi

# 1. Build the original project and apply a patch.
if ! "$SYS4C" build --output-dir="$wintmp" --no-debug-info src/patch.pje ||
   ! "$SYS4C" patch src/patch.pje --base-ain "$wintmp/base.ain" \
       --source src/patch.jaf --no-debug-info -o "$wintmp/patched.ain"; then
	echo "patch: FAIL (patch compilation failed)"
	exit 1
fi

# 2. Decompile the result and check functions and newly added types.
if ! "$SYS4DC" -o "$wintmp/patched" "$wintmp/patched.ain"; then
	echo "patch: FAIL (decompilation failed)"
	exit 1
fi

if ! grep -R -F 'return fresh(value);' "$tmp/patched" >/dev/null ||
   ! grep -R -F 'return value + 1;' "$tmp/patched" >/dev/null ||
   ! grep -R -F 'class NewClass' "$tmp/patched" >/dev/null ||
   ! grep -R -F 'class NewStruct' "$tmp/patched" >/dev/null ||
   ! grep -R -F 'functype int Callback' "$tmp/patched" >/dev/null ||
   ! grep -R -F 'delegate void EventHandler' "$tmp/patched" >/dev/null; then
	echo "patch: FAIL (patched functions or types were not decompiled)"
	exit 1
fi

# 3. The decompiled patch result must be accepted by the compiler.
mkdir -p "$tmp/rebuilt"
project="$tmp/patched/patched.pje"
if command -v cygpath >/dev/null 2>&1; then
	project=$(cygpath -m "$project")
fi
if ! "$SYS4C" build --output-dir="$wintmp/rebuilt" --no-debug-info "$project"; then
	echo "patch: FAIL (decompiled project could not be rebuilt)"
	exit 1
fi

echo "patch: PASS"
