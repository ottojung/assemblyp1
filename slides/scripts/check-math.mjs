// Slidev renders Markdown $...$ and $$...$$, not \(..\) or \[..\].
// A successful build alone does not detect when the latter render as text.
import { readFileSync } from 'node:fs'
import { fileURLToPath } from 'node:url'
import { dirname, join } from 'node:path'

const root = join(dirname(fileURLToPath(import.meta.url)), '..')
let problems = 0
for (const name of ['programmers', 'biologists']) {
  const lines = readFileSync(join(root, name + '.md'), 'utf8').split('\n')
  for (let i = 0; i < lines.length; i++) {
    if (/\\[()[\]]/.test(lines[i])) {
      console.error(name + '.md:' + (i + 1) +
        ': unsupported TeX math delimiter; use $...$ or $$...$$')
      problems++
    }
  }
}
if (problems > 0) process.exit(1)
console.log('check-math: OK (both decks use Slidev-supported delimiters)')
