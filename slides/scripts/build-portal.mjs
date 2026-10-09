import { cpSync, existsSync, mkdirSync, readdirSync, rmSync } from 'node:fs'
import { dirname, join } from 'node:path'
import { fileURLToPath } from 'node:url'

const here = dirname(fileURLToPath(import.meta.url))
const slidesDir = join(here, '..')
const portalDir = join(slidesDir, 'portal')
const distDir = join(slidesDir, 'dist')

if (!existsSync(portalDir)) {
  console.error(`build-portal: missing portal directory at ${portalDir}`)
  process.exit(1)
}

mkdirSync(distDir, { recursive: true })

for (const entry of readdirSync(portalDir)) {
  const from = join(portalDir, entry)
  const to = join(distDir, entry)
  rmSync(to, { recursive: true, force: true })
  cpSync(from, to, { recursive: true })
}

console.log(`build-portal: copied ${portalDir} -> ${distDir}`)
