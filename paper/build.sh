#!/usr/bin/env sh
# Reproducible PDF build for the AssemblyP1 white paper.
#
# Uses a pinned Guix manifest and a local profile (kept inside this directory
# and ignored by git, so no writable per-user Guix profile is required).
# Runs latexmk with pdflatex + biber.
set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
cd "$here"

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
