import { existsSync, readFileSync, statSync } from 'node:fs'
import { dirname, join, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const here = dirname(fileURLToPath(import.meta.url))
const slidesDir = join(here, '..')
const distDir = join(slidesDir, 'dist')

const errors = []

function fail(message) {
  errors.push(message)
}

function mustExist(path, what) {
  if (!existsSync(path)) {
    fail(`missing ${what}: ${path}`)
    return false
  }
  return true
}

const decks = [
  { name: 'programmers', base: '/assemblyp1/programmers/' },
  { name: 'biologists', base: '/assemblyp1/biologists/' },
]

const portal = join(distDir, 'index.html')
if (mustExist(portal, 'portal entry')) {
  const html = readFileSync(portal, 'utf8')
  for (const deck of decks) {
    if (!html.includes(`./${deck.name}/`) && !html.includes(`${deck.name}/`)) {
      fail(`portal does not link to ${deck.name}/`)
    }
  }
}

for (const deck of decks) {
  const dir = join(distDir, deck.name)
  const entry = join(dir, 'index.html')
  if (!mustExist(entry, `${deck.name} entry`)) continue

  const html = readFileSync(entry, 'utf8')

  if (!html.includes(deck.base)) {
    fail(`${deck.name}/index.html does not use expected base ${deck.base}`)
  }
  if (html.includes('href="/assets/') || html.includes('src="/assets/')) {
    fail(`${deck.name}/index.html references a root /assets/ path`)
  }

  const refs = new Set()
  const attrRe = /(?:src|href)="([^"]+)"/g
  for (const match of html.matchAll(attrRe)) {
    const url = match[1]
    if (!url.startsWith(deck.base)) continue
    const withoutBase = url.slice(deck.base.length).split(/[?#]/)[0]
    if (!withoutBase) continue
    refs.add(withoutBase)
  }

  for (const ref of refs) {
    const target = resolve(dir, ref)
    if (!target.startsWith(resolve(dir))) {
      fail(`${deck.name}: asset escapes its output directory: ${ref}`)
      continue
    }
    if (!existsSync(target) || !statSync(target).isFile()) {
      fail(`${deck.name}: referenced asset is missing: ${deck.base}${ref}`)
    }
  }

  if (refs.size === 0) {
    fail(`${deck.name}: no base-prefixed assets found; build may be malformed`)
  }
}

if (errors.length > 0) {
  console.error('validate-dist: FAILED')
  for (const error of errors) console.error(`  - ${error}`)
  process.exit(1)
}

console.log('validate-dist: OK (portal + both decks, base paths and assets verified)')
