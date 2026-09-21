;; Minimal, pinned TeX dependency set for the AssemblyP1 Beamer talk.
;; Build with: guix shell -m manifest.scm -- latexmk -pdf main.tex
;; (or simply run talk/build.sh)
(specifications->manifest
 '("texlive-scheme-basic"   ; pdflatex, latex, core LaTeX
   "texlive-latexmk"        ; driver
   "texlive-beamer"         ; beamer class + themes
   "texlive-pgf"            ; TikZ figures
   "texlive-xcolor"         ; color
   "texlive-booktabs"       ; professional tables
   "texlive-hyperref"       ; hyperlinks
   "texlive-lm"))           ; scalable Latin Modern fonts
