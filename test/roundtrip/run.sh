#!/bin/bash
#
# Lightweight round-trip test: compile the project under src/, decompile the
# resulting .ain, and verify that the decompiled project is byte-for-byte
# identical to src/.

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

# 1. Compile the project.
if ! "$SYS4C" build --output-dir="$wintmp" --no-debug-info src/roundtrip.pje; then
	echo "roundtrip: FAIL (compilation failed)"
	exit 1
fi

# 2. Decompile the resulting .ain back into a project.
if ! "$SYS4DC" -o "$wintmp/out" "$wintmp/roundtrip.ain"; then
	echo "roundtrip: FAIL (decompilation failed)"
	exit 1
fi

# Drop debug_info.json before comparing.
rm -f "$tmp/out/debug_info.json"

# 3. The decompiled project must be identical to src/.
if ! diff -ru src "$tmp/out"; then
	echo "roundtrip: FAIL (decompiled project differs from src/)"
	exit 1
fi

echo "roundtrip: PASS"
