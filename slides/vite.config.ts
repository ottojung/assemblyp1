import { defineConfig } from 'vite'

// Slidev 53 ships Vite 8, whose default CSS minifier (lightningcss) rejects
// some UnoCSS-generated rules from the default theme. Disabling CSS
// minification keeps the build deterministic and correct; JS is still minified.
export default defineConfig({
  build: {
    cssMinify: false,
  },
})
