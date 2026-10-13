// Slidev Markdown must not be hidden inside raw HTML blocks.
// This guards against literal ** and other Markdown punctuation on slides.
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, join } from 'node:path'

const root = join(dirname(fileURLToPath(import.meta.url)), '..')
let errors = 0
for (const deck of ['programmers', 'biologists']) {
  const lines = readFileSync(join(root, deck + '.md'), 'utf8').split('\n')
  let fenced = false, comment = false, displayMath = false
  for (let i = 0; i < lines.length; i++) {
    const raw = lines[i]
    const trim = raw.trim()
    if (trim.startsWith('<!--')) comment = true
    if (comment) {
      if (trim.includes('-->')) comment = false
      continue
    }
    if (/^(`{3,}|~{3,})/.test(trim)) { fenced = !fenced; continue }
    if (fenced) continue
    if (trim === '$$') { displayMath = !displayMath; continue }
    if (displayMath) continue
    const fail = (reason) => {
      console.error(deck + '.md:' + (i + 1) + ': ' + reason)
      errors++
    }
    if (/<\/?div(?:\s|>)/i.test(raw)) {
      fail('raw HTML div blocks hide Markdown; use Markdown instead')
    }
    if (/`[^`]*\*\*[^`]*`/.test(raw)) {
      fail('bold markers inside an inline code span')
    }
    if ((raw.match(/\*\*/g) || []).length % 2 !== 0) {
      fail('unpaired Markdown bold marker')
    }
  }
  if (fenced || comment || displayMath) {
    console.error(deck + '.md: unterminated fence, comment, or display math')
    errors++
  }
}
if (errors) process.exit(1)
console.log('check-format: OK (Markdown emphasis and layout are renderable)')
