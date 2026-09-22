#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
exec guix shell -m manifest.scm -- latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
