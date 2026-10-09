# AssemblyP1 presentations (Slidev)

Two independent [Slidev](https://sli.dev) decks that share one GitHub Pages
site:

- **`programmers.md`** — mathematics plus the engineering story of how a
  multi-agent research system produced kernel-checked results (board #251).
- **`biologists.md`** — what short-read sequencing can reveal, and what has
  been proved about population likelihood (board #250).
- **`portal/`** — the landing page that forks left to programmers and right to
  biologists (board #252). The checked-in page is a scaffold provided by the
  infrastructure work; the experience owner replaces it.

This project replaces the former Beamer toolchain. The LaTeX white paper under
[`../paper/`](../paper/) is unrelated and remains in place.

## Requirements

- Node.js `>= 22.12` (pinned in `package.json`; CI uses Node 22).
- `npm`.

## Local development

```sh
cd slides
npm ci

# Live-reload one deck at a time:
npm run dev:programmers
npm run dev:biologists
```

`npm ci` installs exactly the versions recorded in `package-lock.json`. Use
`npm ci` (not `npm install`) for reproducible installs; only run
`npm install` when you intentionally change `package.json`.

## Build

```sh
cd slides
npm run build
```

`npm run build` cleans `dist/` once, then:

1. builds `programmers.md` to `dist/programmers/` at base `/assemblyp1/programmers/`,
2. builds `biologists.md` to `dist/biologists/` at base `/assemblyp1/biologists/`,
3. copies `portal/` to `dist/` (the site root),
4. runs `npm run validate` to check that the portal and both decks exist, use
   the expected base paths, and reference only assets that were actually
   produced.

Individual steps are available as `npm run build:programmers`,
`npm run build:biologists`, `npm run build:portal`, `npm run clean`, and
`npm run validate`.

Speaker notes are excluded from the public build with Slidev's
`--without-notes` flag.

## Preview the built site

The built site assumes it is served under the `/assemblyp1/` prefix, matching
the GitHub Pages project URL. Use the bundled static server:

```sh
cd slides
npm run preview
# portal:      http://localhost:4173/assemblyp1/
# programmers: http://localhost:4173/assemblyp1/programmers/
# biologists:  http://localhost:4173/assemblyp1/biologists/
```

Both decks use Slidev's `routerMode: hash`, so direct slide links such as
`/assemblyp1/programmers/#/5` survive a hard refresh on GitHub Pages without a
server rewrite.

## Deployment

`.github/workflows/pages.yml` builds the site and deploys `slides/dist` with the
official `configure-pages` / `upload-pages-artifact` / `deploy-pages` actions:

- pull requests build and validate the static site but do not deploy;
- pushes to `main` and manual `workflow_dispatch` runs deploy to GitHub Pages.

GitHub Pages must use **GitHub Actions** as its source (Settings → Pages →
Build and deployment → Source). The workflow asks `configure-pages` to enable
this automatically, but a repository admin may need to confirm the setting the
first time.

## Layout

```text
slides/
  package.json          pinned dependencies and build scripts
  package-lock.json     reproducible npm ci lockfile
  vite.config.ts        disables CSS minification (see comment)
  programmers.md        programmers' deck entry
  biologists.md         biologists' deck entry
  components/           shared Slidev/Vue components
  portal/index.html     landing page (scaffold; owned by #252)
  scripts/              portal assembly, validation, static preview
  dist/                 generated site (git-ignored)
```

## Coordination contract

Other issues can rely on these stable paths:

- build root: `slides/`
- deck entries: `slides/programmers.md`, `slides/biologists.md`
- published entry points: `/assemblyp1/`, `/assemblyp1/programmers/`,
  `/assemblyp1/biologists/`
- Pages artifact: `slides/dist`

Content owners edit only their own Markdown entry (and, if needed, shared
components); infrastructure changes to `package.json`, the lockfile, the
workflows, or `scripts/` belong to the infrastructure issue.
