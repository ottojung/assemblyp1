#!/usr/bin/env sh
# Reproducible PDF build for the AssemblyP1 white paper.
#
# Uses a pinned Guix manifest and a local profile (kept inside this directory
# and ignored by git, so no writable per-user Guix profile is required).
# Runs latexmk with pdflatex + biber.
set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$here"

# Keep PDF creation timestamps reproducible from the checked-out source.
# Honor an explicitly supplied SOURCE_DATE_EPOCH (e.g. by reproducible builders).
if [ -z "${SOURCE_DATE_EPOCH:-}" ] && git rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  SOURCE_DATE_EPOCH=$(git log -1 --format=%ct)
  export SOURCE_DATE_EPOCH
fi


profile="$here/.guix-profile"
if [ ! -x "$profile/bin/latexmk" ]; then
  guix package -m manifest.scm -p "$profile"
fi

GUIX_PROFILE="$profile"
export GUIX_PROFILE
# The generated profile may reference unset variables; tolerate that.
set +u
# shellcheck disable=SC1091
. "$profile/etc/profile"
set -u

exec latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex "$@"
