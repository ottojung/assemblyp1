;; Minimal, pinned TeX dependency set for the AssemblyP1 white paper.
;; Build with: guix shell -m manifest.scm -- latexmk -pdf main.tex
;; (or simply run paper/build.sh)
(specifications->manifest
 '("texlive-scheme-basic"   ; pdflatex, latex, bibtex, core LaTeX
   "texlive-latexmk"        ; driver
   "texlive-biblatex"       ; bibliography engine
   "texlive-biber"          ; biblatex backend
   "texlive-amsmath"        ; amsmath
   "texlive-amsfonts"       ; amssymb
   "texlive-amscls"         ; amsthm
   "texlive-geometry"       ; page layout
   "texlive-hyperref"       ; hyperlinks, \autoref
   "texlive-booktabs"       ; professional tables
   "texlive-microtype"      ; typographic refinement
   "texlive-enumitem"       ; list customization
   "texlive-xcolor"         ; color
   "texlive-pgf"            ; TikZ figures
   "texlive-lm"))           ; scalable Latin Modern fonts
