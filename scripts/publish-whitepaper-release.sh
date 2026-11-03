#!/usr/bin/env bash
# Publish the built white paper under a stable, intentionally moving Release tag.
set -euo pipefail
pdf="${1:?usage: publish-whitepaper-release.sh path/to/main.pdf path/to/assemblyp1-arxiv-source.zip}"
source_zip="${2:?usage: publish-whitepaper-release.sh path/to/main.pdf path/to/assemblyp1-arxiv-source.zip}"
test -s "$source_zip"
test "$(basename "$source_zip")" = "assemblyp1-arxiv-source.zip"
: "${GH_TOKEN:?}"
: "${GITHUB_REPOSITORY:?}"
: "${GITHUB_SHA:?}"
test -s "$pdf"
test "$(head -c 5 "$pdf")" = "%PDF-"
tag="whitepaper-latest"
asset_name="assemblyp1-white-paper.pdf"
title="AssemblyP1 white paper (current main)"
# GitHub uses the actual basename as the URL; hash suffixes are labels only.
asset_path="$(dirname "$pdf")/$asset_name"
cp "$pdf" "$asset_path"
notes="Automatically compiled from main and updated after successful document builds. Download the PDF or standalone arXiv-ready LaTeX source ZIP. Repository: https://github.com/${GITHUB_REPOSITORY}"
if gh release view "$tag" --repo "$GITHUB_REPOSITORY" >/dev/null 2>&1; then
  gh release upload "$tag" "$asset_path" "$source_zip" --clobber --repo "$GITHUB_REPOSITORY"
  gh release edit "$tag" --title "$title" --notes "$notes" --repo "$GITHUB_REPOSITORY"
  # Remove the old main.pdf asset from the initial rollout, if present.
  if gh release view "$tag" --json assets --jq '.assets[].name' --repo "$GITHUB_REPOSITORY" | grep -Fxq main.pdf; then
    gh release delete-asset "$tag" main.pdf --yes --repo "$GITHUB_REPOSITORY"
  fi
  # Keep the source archive synchronized with the asset for this rolling tag.
  gh api --method PATCH "repos/${GITHUB_REPOSITORY}/git/refs/tags/${tag}" \
    -f sha="$GITHUB_SHA" -F force=true >/dev/null
else
  gh release create "$tag" "$asset_path" "$source_zip" \
    --target "$GITHUB_SHA" --title "$title" --notes "$notes" \
    --latest=false --repo "$GITHUB_REPOSITORY"
fi
gh api "repos/${GITHUB_REPOSITORY}/releases/tags/${tag}" \
  --jq '.assets[] | select(.name == "assemblyp1-white-paper.pdf") | .browser_download_url'
