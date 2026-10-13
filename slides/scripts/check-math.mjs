// Slidev parses $...$ / $$...$$ math in Markdown, but neither TeX's
// \( ... \) and \[ ... \] delimiters nor math inside raw HTML div blocks.
// Both errors otherwise leave literal TeX or dollar signs on slides.
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, join } from 'node:path'

const root = join(dirname(fileURLToPath(import.meta.url)), '..')
let problems = 0
for (const name of ['programmers', 'biologists']) {
  const lines = readFileSync(join(root, name + '.md'), 'utf8').split('\n')
  let divDepth = 0
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]
    const opens = (line.match(/<div(?:\s|>)/g) || []).length
    const closes = (line.match(/<\/div>/g) || []).length
    if (/\\[()[\]]/.test(line)) {
      console.error(name + '.md:' + (i + 1) +
        ': unsupported TeX math delimiters; use Markdown $...$ or $$...$$')
      problems++
    }
    if (divDepth + opens > 0 && line.includes('$')) {
      console.error(name + '.md:' + (i + 1) +
        ': math inside a literal HTML div appears as source; move it into Markdown')
      problems++
    }
    divDepth += opens - closes
  }
}
if (problems > 0) process.exit(1)
console.log('check-math: OK (math is in renderable Markdown in both decks)')
