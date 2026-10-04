#!/usr/bin/env bash
# Board 94 green-readiness measurement harness (read-only w.r.t. the library).
#
# Usage: scripts/board94_green_measure.sh <name> <ref>
#
# Creates a throwaway git worktree under $GA_ROOT (default /workspace/ga94 --
# it must be on the SAME btrfs subvolume as $GA_LAKE_SRC, because hardlinks
# cannot cross subvolumes; a first attempt under /tmp/opencode silently
# re-cloned Mathlib and OOM-killed the build, see the report),
# hardlink-clones a prebuilt .lake from $GA_LAKE_SRC (default
# /workspace/assemblyp1-94-leone/.lake) so Mathlib oleans are reused, then runs
# `lake build` (the default target) and prints the exit code plus the failing
# modules.  Nothing in any live worktree is modified.
#
# 94f16 amendment: the hardlink-cloned .lake can carry PROJECT oleans built from
# a different source tree, and the report's own section 0 records a red that was
# such a stale olean rather than a real defect.  So unless GA_KEEP_OLEANS=1, all
# AssemblyP1 project oleans are deleted first (Mathlib is untouched); no recorded
# green can then be inherited from a stale olean.
set -u
name="$1"; ref="$2"
GA_ROOT="${GA_ROOT:-/workspace/ga94}"
GA_LAKE_SRC="${GA_LAKE_SRC:-/workspace/assemblyp1-94-leone/.lake}"
repo="$(git rev-parse --show-toplevel)"
wt="$GA_ROOT/$name"
mkdir -p "$GA_ROOT"
if [ ! -d "$wt" ]; then
  git -C "$repo" worktree add --detach "$wt" "$ref" >/dev/null || exit 90
fi
if [ ! -e "$wt/.lake" ]; then
  cp -al "$GA_LAKE_SRC" "$wt/.lake"
fi
cd "$wt" || exit 91
if [ "${GA_KEEP_OLEANS:-0}" != "1" ]; then
  rm -f "$wt"/.lake/build/lib/lean/AssemblyP1*.olean \
        "$wt"/.lake/build/lib/lean/AssemblyP1*.ilean \
        "$wt"/.lake/build/lib/lean/AssemblyP1*.hash \
        "$wt"/.lake/build/lib/lean/AssemblyP1.olean \
        "$wt"/.lake/build/lib/lean/AssemblyP1.ilean \
        "$wt"/.lake/build/ir/AssemblyP1*.c 2>/dev/null
fi
start=$(date +%s)
lake build >"$wt/build.log" 2>&1
rc=$?
end=$(date +%s)
echo "=== $name ref=$ref sha=$(git rev-parse --short HEAD) exit=$rc seconds=$((end-start))"
grep -E "^(error|warning: declaration uses)" "$wt/build.log" | sed 's/^/    /' | head -60
echo "    (log: $wt/build.log)"
exit $rc
