#!/usr/bin/env node
// Acceptance tests for the AssemblyP1 GitHub Pages portal and decks (board #252).
//
// Usage:
//   node scripts/acceptance-pages.mjs [--dist slides/dist] [--url https://ottojung.github.io/assemblyp1/] [--shots DIR]
//
// Without --url the script serves the built dist/ tree locally under the
// /assemblyp1/ project prefix (mirroring GitHub Pages) and runs there.
// With --url the same browser checks run against a live deployment.
//
// Requires chromedriver and chromium on PATH (started automatically if down).

import { execSync, spawn } from 'node:child_process'
import {
  existsSync,
  mkdirSync,
  openSync,
  readdirSync,
  readFileSync,
  statSync,
  writeFileSync,
} from 'node:fs'
import { createServer } from 'node:http'
import { createReadStream } from 'node:fs'
import { dirname, extname, join, normalize, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const here = dirname(fileURLToPath(import.meta.url))

// ---------------------------------------------------------------- arguments
const args = process.argv.slice(2)
function argValue(flag) {
  const i = args.indexOf(flag)
  return i >= 0 ? args[i + 1] : undefined
}
const distDir = resolve(argValue('--dist') ?? join(here, '..', 'slides', 'dist'))
const liveUrl = argValue('--url')
const shotsDir = resolve(argValue('--shots') ?? join(here, '..', 'acceptance-shots'))
const prefix = '/assemblyp1'

// WebDriver key code points (PUA range per the WebDriver spec).
const ARROW_RIGHT = '\uE014'
const ARROW_LEFT = '\uE012'
const ENTER = '\uE007'
const TAB = '\uE004'

// ---------------------------------------------------------------- utilities
let failures = 0
let passes = 0
const failuresList = []
function check(name, ok, detail = '') {
  if (ok) {
    passes += 1
    console.log(`  PASS  ${name}`)
  } else {
    failures += 1
    failuresList.push(name + (detail ? ` — ${detail}` : ''))
    console.log(`  FAIL  ${name}${detail ? ` — ${detail}` : ''}`)
  }
}

const sleep = (ms) => new Promise((r) => setTimeout(r, ms))

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.svg': 'image/svg+xml',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.webp': 'image/webp',
  '.woff': 'font/woff',
  '.woff2': 'font/woff2',
  '.ico': 'image/x-icon',
}

// ---------------------------------------------------------------- static checks
function staticChecks() {
  console.log('\n== static checks ==')
  check('dist exists', existsSync(distDir), distDir)

  const portal = join(distDir, 'index.html')
  check('portal index.html exists', existsSync(portal))
  if (!existsSync(portal)) return

  const html = readFileSync(portal, 'utf8')
  check('portal has <!doctype html>', /^<!doctype html>/i.test(html))
  check('portal lang="en"', /<html lang="en"/.test(html))
  check('portal has charset utf-8', /charset="?utf-8/i.test(html))
  check('portal has viewport meta', /name="viewport"[^>]+width=device-width/.test(html))
  check(
    'portal title',
    /<title>AssemblyP1 — choose your path<\/title>/.test(html),
    'expected "AssemblyP1 — choose your path"',
  )
  check('portal has meta description', /name="description"/.test(html))
  check('portal has skip link', /class="skip-link"/.test(html) && /href="#paths"/.test(html))
  check('portal has one h1', (html.match(/<h1[ >]/g) || []).length === 1)
  check('portal has main#paths', /<main id="paths">/.test(html))
  check('portal links to ./programmers/', /href="\.\/programmers\/"/.test(html))
  check('portal links to ./biologists/', /href="\.\/biologists\/"/.test(html))
  check('portal has Left direction label', /Left/.test(html))
  check('portal has Right direction label', /Right/.test(html))
  check(
    'portal paths have aria-labels',
    (html.match(/aria-label="[^"]+presentation for (programmers|biologists)/g) || []).length === 2,
  )
  check('portal styles focus-visible', /:focus-visible/.test(html))
  check('portal handles reduced motion', /prefers-reduced-motion/.test(html))
  check('portal declares dark color-scheme', /color-scheme:\s*dark/.test(html))
  check(
    'portal loads no external resources',
    !/(src|href)="https?:\/\//.test(html.replace(/xmlns="http:\/\/www\.w3\.org\/2000\/svg"/g, '')),
    'no http(s) src/href (no CDNs/trackers)',
  )

  for (const [name, title] of [
    ['programmers', 'AssemblyP1 for Programmers - Slidev'],
    ['biologists', 'AssemblyP1 for Biologists - Slidev'],
  ]) {
    const entry = join(distDir, name, 'index.html')
    check(`${name}/index.html exists`, existsSync(entry))
    if (!existsSync(entry)) continue
    const deck = readFileSync(entry, 'utf8')
    check(`${name} title`, deck.includes(`<title>${title}</title>`), title)
    check(`${name} uses its base path`, deck.includes(`${prefix}/${name}/`))
    // The home link is rendered client Vue, so the marker lives in the deck's
    // JS bundles rather than the static HTML shell.
    const bundleTexts = []
    const collectJs = (dir) => {
      for (const f of readdirSync(dir)) {
        const p = join(dir, f)
        if (statSync(p).isDirectory()) collectJs(p)
        else if (f.endsWith('.js')) bundleTexts.push(readFileSync(p, 'utf8'))
      }
    }
    collectJs(join(distDir, name, 'assets'))
    const bundles = bundleTexts.join('\n')
    check(
      `${name} has back-to-root home link`,
      bundles.includes('ap1-home') && bundles.includes('Choose another audience'),
    )
  }

  // Sensitive-content scan of the whole published tree. High-signal secrets
  // only: framework bundles legitimately mention localhost or presenter-sync
  // query params, so generic host/keyword patterns are not treated as leaks.
  const sensitive = [
    /supabase\.co/i,
    /service_role/i,
    /anon[_-]?key/i,
    /BEGIN [A-Z ]*PRIVATE KEY/,
    /api[_-]?key\s*[:=]\s*['"][^'"]{8,}['"]/i,
    /marceline/i,
  ]
  const hits = []
  function walk(dir) {
    let entries
    try {
      entries = readdirSync(dir)
    } catch {
      return
    }
    for (const entry of entries) {
      const p = join(dir, entry)
      if (statSync(p).isDirectory()) {
        walk(p)
      } else if (/\.(html?|js|mjs|css|json|svg|txt|md)$/i.test(entry)) {
        let text
        try {
          text = readFileSync(p, 'utf8')
        } catch {
          continue
        }
        for (const re of sensitive) {
          if (re.test(text)) hits.push(`${p}: ${re}`)
        }
      }
    }
  }
  walk(distDir)
  check('no sensitive strings in public build', hits.length === 0, hits.slice(0, 5).join('; '))
}

// ---------------------------------------------------------------- chromedriver
async function withChromedriver(fn) {
  async function running() {
    try {
      const r = await fetch('http://127.0.0.1:9515/status')
      return r.ok
    } catch {
      return false
    }
  }
  const wasRunning = await running()
  let child = null
  if (!wasRunning) {
    mkdirSync(join(here, '..', '.tmp-acceptance'), { recursive: true })
    const log = openSync(join(here, '..', '.tmp-acceptance', 'chromedriver.log'), 'w')
    child = spawn('chromedriver', ['--port=9515', '--allowed-ips=127.0.0.1', '--allowed-origins=*'], {
      stdio: ['ignore', log, log],
    })
    child.unref()
    for (let i = 0; i < 60; i += 1) {
      await sleep(250)
      if (await running()) break
    }
    if (!(await running())) throw new Error('chromedriver did not start')
  }
  try {
    await fn()
  } finally {
    if (child) child.kill('SIGTERM')
  }
}

// ---------------------------------------------------------------- browser checks
async function browserChecks(base) {
  console.log(`\n== browser acceptance (${base}) ==`)
  mkdirSync(shotsDir, { recursive: true })

  let sid = null
  const notFound = new Set()
  const call = async (method, path, body) => {
    const res = await fetch(`http://127.0.0.1:9515${path}`, {
      method,
      headers: { 'content-type': 'application/json' },
      body: body === undefined ? undefined : JSON.stringify(body),
    })
    const text = await res.text()
    let json
    try {
      json = JSON.parse(text)
    } catch {
      json = { raw: text }
    }
    if (json.value && json.value.error) {
      throw new Error(`${method} ${path}: ${json.value.error} ${(json.value.message ?? '').slice(0, 160)}`)
    }
    return json.value
  }
  const sh = (script) => call('POST', `/session/${sid}/execute/sync`, { script, args: [] })
  const key = async (value) => {
    await call('POST', `/session/${sid}/actions`, {
      actions: [{ type: 'key', id: 'kb', actions: [{ type: 'keyDown', value }, { type: 'keyUp', value }] }],
    })
  }

  async function newSession() {
    const { sessionId } = await call('POST', '/session', {
      capabilities: {
        alwaysMatch: {
          'goog:chromeOptions': {
            binary: process.env.CHROME_BIN ?? execSync('which chromium').toString().trim(),
            args: ['--headless=new', '--no-sandbox', '--disable-gpu', '--disable-dev-shm-usage', '--window-size=1280,900'],
          },
        },
      },
    })
    sid = sessionId
    return sid
  }

  async function goto(url, waitMs = 2200) {
    await call('POST', `/session/${sid}/url`, { url })
    await sleep(waitMs)
  }

  async function setViewport(width, height) {
    await call('POST', `/session/${sid}/window/rect`, { width, height })
    await sleep(400)
  }

  async function shot(name) {
    const data = await call('GET', `/session/${sid}/screenshot`)
    writeFileSync(join(shotsDir, `${name}.png`), Buffer.from(data, 'base64'))
  }

  async function failedResources() {
    const entries = await sh(
      `return JSON.stringify(performance.getEntriesByType('resource').filter(e => e.responseStatus >= 400).map(e => e.name))`,
    )
    return JSON.parse(entries ?? '[]')
  }

  async function pageErrors() {
    const errs = await sh(`return JSON.stringify(window.__ap1Errors ?? [])`)
    return JSON.parse(errs ?? '[]')
  }

  async function instrument() {
    await sh(`window.__ap1Errors = []; window.addEventListener('error', e => window.__ap1Errors.push(String(e.message))); true`)
  }

  try {
    await newSession()

    // ---------- root: structure, metadata, click/tap paths
    await goto(`${base}/`)
    check('root: page title', (await sh('return document.title')) === 'AssemblyP1 — choose your path')
    check('root: h1 present', (await sh(`return document.querySelector('h1')?.textContent.trim()`))?.length > 10)
    const hrefs = JSON.parse(
      await sh(`return JSON.stringify(Array.from(document.querySelectorAll('a.path')).map(a => a.getAttribute('href')))`),
    )
    check('root: exactly two path links', hrefs.length === 2, JSON.stringify(hrefs))
    check('root: left link to programmers', hrefs[0] === './programmers/', hrefs[0])
    check('root: right link to biologists', hrefs[1] === './biologists/', hrefs[1])
    check('root: no failed resources', (await failedResources()).length === 0, JSON.stringify(await failedResources()))
    check('root: no JS errors', (await pageErrors()).length === 0, JSON.stringify(await pageErrors()))
    await shot('01-root-desktop')

    // left click
    await sh(`document.querySelector('a.path.left').click(); true`)
    await sleep(1800)
    check('root: left click navigates to programmers deck', (await sh('return location.href')).includes('/programmers/'))
    check('root: programmers deck title', (await sh('return document.title')) === 'AssemblyP1 for Programmers - Slidev')

    // back to root, right click
    await goto(`${base}/`)
    await sh(`document.querySelector('a.path.right').click(); true`)
    await sleep(1800)
    check('root: right click navigates to biologists deck', (await sh('return location.href')).includes('/biologists/'))
    check('root: biologists deck title', (await sh('return document.title')) === 'AssemblyP1 for Biologists - Slidev')

    // ---------- keyboard: arrows move between paths, Enter activates
    await goto(`${base}/`)
    await sh(`document.body.focus(); true`)
    await key(ARROW_LEFT)
    await sleep(250)
    check('keyboard: ArrowLeft focuses left path', (await sh(`return document.activeElement?.classList.contains('left')`)) === true)
    await key(ARROW_RIGHT)
    await sleep(250)
    check('keyboard: ArrowRight focuses right path', (await sh(`return document.activeElement?.classList.contains('right')`)) === true)
    await key(ARROW_LEFT)
    await sleep(250)
    await key(ENTER)
    await sleep(1800)
    check('keyboard: Enter on left path activates it', (await sh('return location.href')).includes('/programmers/'))
    check('keyboard: programmers deck reached via keyboard', (await sh('return document.title')) === 'AssemblyP1 for Programmers - Slidev')

    // ---------- tab order + visible focus
    await goto(`${base}/`)
    await sh(`document.activeElement?.blur?.(); true`)
    await key(TAB)
    await sleep(200)
    check('keyboard: first Tab reaches skip link', (await sh(`return document.activeElement?.classList.contains('skip-link')`)) === true)
    await key(TAB)
    await sleep(200)
    check('keyboard: second Tab reaches left path', (await sh(`return document.activeElement?.classList.contains('left')`)) === true)
    const outline = JSON.parse(
      await sh(
        `return JSON.stringify((() => { const a = document.activeElement; const cs = getComputedStyle(a); return { style: cs.outlineStyle, width: cs.outlineWidth, color: cs.outlineColor }; })())`,
      ),
    )
    check('keyboard: focus outline visible', outline.style !== 'none' && parseFloat(outline.width) > 0, JSON.stringify(outline))
    await shot('02-root-focus-visible')

    // ---------- hard reload (direct entry) on each deck + root
    for (const [label, path, title] of [
      ['root', '/', 'AssemblyP1 — choose your path'],
      ['programmers', '/programmers/', 'AssemblyP1 for Programmers - Slidev'],
      ['biologists', '/biologists/', 'AssemblyP1 for Biologists - Slidev'],
    ]) {
      await goto(`${base}${path}`, 2600)
      await sh(`location.reload(); true`)
      await sleep(2600)
      check(`hard reload ${label}: title survives`, (await sh('return document.title')) === title)
      const failed = await failedResources()
      check(`hard reload ${label}: no failed resources`, failed.length === 0, JSON.stringify(failed.slice(0, 4)))
      const notFoundHere = [...notFound]
      check(`hard reload ${label}: no 404s`, notFoundHere.length === 0, notFoundHere.join(', '))
      await instrument()
    }

    // ---------- back-to-root from each deck
    for (const [label, path] of [
      ['programmers', '/programmers/'],
      ['biologists', '/biologists/'],
    ]) {
      await goto(`${base}${path}`, 2400)
      const homeHref = await sh(`return document.querySelector('a.ap1-home')?.getAttribute('href')`)
      check(`deck ${label}: back-to-root link present`, !!homeHref, String(homeHref))
      await sh(`document.querySelector('a.ap1-home').click(); true`)
      await sleep(1800)
      const href = await sh('return location.href')
      check(`deck ${label}: home link returns to root`, href === `${base}/` || href === `${base}`, href)
      check(`deck ${label}: root title after return`, (await sh('return document.title')) === 'AssemblyP1 — choose your path')
    }

    // ---------- slide navigation + presenter mode
    for (const [label, path] of [
      ['programmers', '/programmers/'],
      ['biologists', '/biologists/'],
    ]) {
      await goto(`${base}${path}`, 2400)
      const before = await sh('return location.hash')
      await key(ARROW_RIGHT)
      await sleep(800)
      const after = await sh('return location.hash')
      check(`deck ${label}: ArrowRight advances a slide`, before !== after, `${before} -> ${after}`)
      await key(ARROW_LEFT)
      await sleep(800)
      check(`deck ${label}: ArrowLeft goes back`, (await sh('return location.hash')) === before)
      await shot(`03-deck-${label}`)

      await goto(`${base}${path}#/presenter/1`, 2600)
      const ptitle = await sh('return document.title')
      check(`deck ${label}: presenter mode loads`, ptitle.includes('Presenter'), ptitle)
      const pfailed = await failedResources()
      check(`deck ${label}: presenter mode no failed resources`, pfailed.length === 0, JSON.stringify(pfailed.slice(0, 4)))
      await shot(`04-deck-${label}-presenter`)
    }

    // ---------- mobile layout (390x844): stacking preserves left/right
    await setViewport(390, 844)
    await goto(`${base}/`, 2400)
    const boxes = JSON.parse(
      await sh(
        `return JSON.stringify(Array.from(document.querySelectorAll('a.path')).map(a => { const r = a.getBoundingClientRect(); return { left: a.classList.contains('left'), x: r.x, y: r.y, w: r.width, h: r.height }; }))`,
      ),
    )
    check(
      'mobile: both paths rendered with sane geometry',
      boxes.every((b) => b.w > 100 && b.h > 100 && b.x >= 0 && b.x + b.w <= 390),
      JSON.stringify(boxes),
    )
    check('mobile: paths stacked (left above right)', boxes[0].y < boxes[1].y, JSON.stringify(boxes))
    check(
      'mobile: right path reachable by scrolling',
      (await sh(`document.querySelector('a.path.right').scrollIntoView(); const r = document.querySelector('a.path.right').getBoundingClientRect(); return JSON.stringify({ y: r.y, h: r.height, vh: window.innerHeight })`)).length > 2,
    )
    check('mobile: no horizontal overflow', (await sh('return document.documentElement.scrollWidth')) <= 390)
    const labels = await sh(`return JSON.stringify(Array.from(document.querySelectorAll('.dir')).map(d => d.textContent.trim()))`)
    check('mobile: explicit Left/Right labels', labels.includes('Left') && labels.includes('Right'), labels)
    await shot('05-root-mobile')
    await goto(`${base}/programmers/`, 2400)
    check('mobile: deck loads', (await sh('return document.title')) === 'AssemblyP1 for Programmers - Slidev')
    check('mobile: deck no horizontal overflow', (await sh('return document.documentElement.scrollWidth')) <= 390)
    await shot('06-deck-mobile')

    // ---------- projector layout (1920x1080): unmistakable left/right
    await setViewport(1920, 1080)
    await goto(`${base}/`, 2400)
    const pboxes = JSON.parse(
      await sh(
        `return JSON.stringify(Array.from(document.querySelectorAll('a.path')).map(a => { const r = a.getBoundingClientRect(); return { left: a.classList.contains('left'), cx: r.x + r.width / 2 }; }))`,
      ),
    )
    check('projector: paths side by side', pboxes[0].cx < pboxes[1].cx, JSON.stringify(pboxes))
    check('projector: no failed resources', (await failedResources()).length === 0)
    await shot('07-root-projector')
  } finally {
    if (sid) {
      try {
        await call('DELETE', `/session/${sid}`)
      } catch {
        /* ignore */
      }
    }
  }
}

// ---------------------------------------------------------------- local server
function startLocalServer() {
  const server = createServer((req, res) => {
    let pathname
    try {
      pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname)
    } catch {
      res.writeHead(400)
      return res.end()
    }
    if (pathname === '/') {
      res.writeHead(302, { location: `${prefix}/` })
      return res.end()
    }
    if (!pathname.startsWith(prefix)) {
      res.writeHead(404)
      return res.end()
    }
    let rel = pathname.slice(prefix.length)
    if (rel === '' || rel === '/') rel = '/index.html'
    if (rel.endsWith('/')) rel += 'index.html'
    const target = resolve(distDir, `.${normalize(rel)}`)
    if (!target.startsWith(distDir) || !existsSync(target) || !statSync(target).isFile()) {
      console.log(`  [server] 404 ${pathname}`)
      res.writeHead(404)
      return res.end()
    }
    res.writeHead(200, { 'content-type': MIME[extname(target).toLowerCase()] ?? 'application/octet-stream' })
    createReadStream(target).pipe(res)
  })
  return new Promise((resolvePromise, reject) => {
    server.listen(0, '127.0.0.1', () => {
      const port = server.address().port
      resolvePromise({ server, url: `http://127.0.0.1:${port}${prefix}` })
    })
    server.on('error', reject)
  })
}

// ---------------------------------------------------------------- main
staticChecks()
if (failures > 0) {
  console.log(`\nstatic checks failed: ${failures}`)
  process.exit(1)
}

if (liveUrl) {
  await withChromedriver(() => browserChecks(liveUrl))
} else {
  const { server, url } = await startLocalServer()
  try {
    await withChromedriver(() => browserChecks(url))
  } finally {
    server.close()
  }
}

console.log(`\n== summary: ${passes} passed, ${failures} failed ==`)
if (failures > 0) {
  console.log('failed checks:')
  for (const f of failuresList) console.log(`  - ${f}`)
  process.exit(1)
}
console.log('acceptance: ALL PASS')
