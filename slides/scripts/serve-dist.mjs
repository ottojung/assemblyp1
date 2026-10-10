import { createReadStream, existsSync, statSync } from 'node:fs'
import { createServer } from 'node:http'
import { dirname, extname, join, normalize, resolve } from 'node:path'
import { fileURLToPath } from 'node:url'

const here = dirname(fileURLToPath(import.meta.url))
const distDir = resolve(join(here, '..', 'dist'))
const prefix = '/assemblyp1'
const port = Number(process.env.PORT || 4173)

if (!existsSync(distDir)) {
  console.error(`serve-dist: no build found at ${distDir}; run "npm run build" first`)
  process.exit(1)
}

const types = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.json': 'application/json; charset=utf-8',
  '.svg': 'image/svg+xml',
  '.png': 'image/png',
  '.jpg': 'image/jpeg',
  '.jpeg': 'image/jpeg',
  '.gif': 'image/gif',
  '.webp': 'image/webp',
  '.woff': 'font/woff',
  '.woff2': 'font/woff2',
  '.ttf': 'font/ttf',
  '.ico': 'image/x-icon',
}

function send(res, status, body, type = 'text/plain; charset=utf-8') {
  res.writeHead(status, { 'content-type': type })
  res.end(body)
}

const server = createServer((req, res) => {
  let pathname
  try {
    pathname = decodeURIComponent(new URL(req.url, 'http://localhost').pathname)
  } catch {
    return send(res, 400, 'Bad request')
  }

  if (!pathname.startsWith(prefix)) {
    if (pathname === '/') {
      res.writeHead(302, { location: `${prefix}/` })
      return res.end()
    }
    return send(res, 404, 'Not found')
  }

  let rel = pathname.slice(prefix.length)
  if (rel === '' || rel === '/') rel = '/index.html'
  if (rel.endsWith('/')) rel += 'index.html'

  const target = resolve(distDir, `.${normalize(rel)}`)
  if (!target.startsWith(distDir)) return send(res, 403, 'Forbidden')
  if (!existsSync(target) || !statSync(target).isFile()) {
    return send(res, 404, `Not found: ${pathname}`)
  }

  const type = types[extname(target).toLowerCase()] || 'application/octet-stream'
  res.writeHead(200, { 'content-type': type })
  createReadStream(target).pipe(res)
})

server.listen(port, () => {
  console.log(`serve-dist: serving ${distDir} at http://localhost:${port}${prefix}/`)
  console.log(`  portal:      http://localhost:${port}${prefix}/`)
  console.log(`  programmers: http://localhost:${port}${prefix}/programmers/`)
  console.log(`  biologists:  http://localhost:${port}${prefix}/biologists/`)
})
